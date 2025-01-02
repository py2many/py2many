# Trace object types that are inserted into Python list.

import ast
from collections.abc import Iterable
from typing import Optional

from py2many.analysis import get_id
from py2many.clike import CLikeTranspiler
from py2many.exceptions import AstNotImplementedError


# TODO: is it slow? is it correct?
def _lookup_class_or_module(name, scopes) -> Optional[ast.ClassDef]:
    for scope in scopes:
        if not isinstance(scope.body, Iterable):
            continue
        for entry in scope.body:
            if isinstance(entry, ast.ClassDef):
                if entry.name == name:
                    return entry
        if hasattr(scope, "imports"):
            for entry in scope.imports:
                if entry.name == name:
                    return entry
    return None


def is_class_or_module(name, scopes):
    entry = _lookup_class_or_module(name, scopes)
    return entry is not None


def is_enum(name, scopes):
    entry = _lookup_class_or_module(name, scopes)
    if entry and hasattr(entry, "bases"):
        bases = {get_id(base) for base in entry.bases}
        enum_bases = {"Enum", "IntEnum", "IntFlag"}
        return bases & enum_bases
    return False


def is_self_arg(name, scopes):
    for scope in scopes:
        for entry in scope.body:
            if isinstance(entry, ast.FunctionDef):
                if len(entry.args.args):
                    first_arg = entry.args.args[0]
                    if get_id(first_arg) == name and hasattr(entry, "self_type"):
                        return True
    return False


def is_list(node):
    """Check if a node was assigned as a list"""
    if isinstance(node, ast.List):
        return True
    elif isinstance(node, ast.Assign):
        return is_list(node.value)
    elif isinstance(node, ast.Name):
        var = node.scopes.find(get_id(node))
        return (
            hasattr(var, "assigned_from")
            and not isinstance(var.assigned_from, ast.FunctionDef)
            and not isinstance(var.assigned_from, ast.For)
            and is_list(var.assigned_from.value)
        )
    else:
        return False


# Searches for the first node of type node_type using
# the given scope (search in reverse order)
def find_node_by_type(node_type, scopes):
    c_node = None
    for i in range(len(scopes) - 1, -1, -1):
        sc = scopes[i]
        if isinstance(sc, node_type):
            c_node = sc
            break
        if hasattr(sc, "body"):
            c_node = find_in_body(sc.body, (lambda x: isinstance(x, node_type)))
            if c_node is not None:
                break
    return c_node


# Finds a node in the given body if it satisfies fn
def find_in_body(body, fn):
    for i in range(len(body) - 1, -1, -1):
        node = body[i]
        if fn(node):
            return node
        elif isinstance(node, ast.Expr) and hasattr(node, "value") and fn(node.value):
            return node.value
        elif hasattr(node, "iter") and fn(node.iter):
            return node.iter
        elif hasattr(node, "test") and fn(node.test):
            return node.test
        elif hasattr(node, "body"):
            ret = find_in_body(node.body, fn)
            if ret:
                return ret

    return None


def value_expr(node):
    """
    Follow all assignments down the rabbit hole in order to find
    the value expression of a name.
    The boundary is set to the current scope.
    """
    return ValueExpressionVisitor().visit(node)


def value_type(node):
    """
    Guess the value type of a node based on the manipulations or assignments
    in the current scope.
    Special case: If node is a container like a list the value type inside the
    list is returned not the list type itself.
    """
    return ValueTypeVisitor().visit(node)


class ValueExpressionVisitor(ast.NodeVisitor):
    def __init__(self):
        super().__init__()
        self._stack = []

    def visit_Constant(self, node):
        return str(node.n)

    def visit_Str(self, node):
        return node.s

    def visit_Name(self, node):
        name = get_id(node)
        if name in self._stack:
            # Avoid infinite recursion in cases like foo = bar(foo)
            return name
        self._stack.append(name)
        try:
            return self._visit_Name(node)
        finally:
            self._stack.pop()

    def _visit_Name(self, node):
        name = get_id(node)
        var = node.scopes.find(name)

        if not var:  # TODO why no scopes found for node id?
            return name

        # TODO: code looks C++ specific. Move out
        if hasattr(var, "assigned_from"):
            if isinstance(var.assigned_from, ast.For):
                it = var.assigned_from.iter
                return "std::declval<typename decltype({})::value_type>()".format(
                    self.visit(it)
                )
            elif isinstance(var.assigned_from, ast.FunctionDef):
                return get_id(var)
            else:
                return self.visit(var.assigned_from.value)
        else:
            return name

    def visit_Call(self, node):
        arg_strings = [self.visit(arg) for arg in node.args]
        arg_strings = [a for a in arg_strings if a is not None]
        params = ",".join(arg_strings)
        return f"{self.visit(node.func)}({params})"

    def visit_Assign(self, node):
        return self.visit(node.value)

    def visit_BinOp(self, node):
        return "{} {} {}".format(
            self.visit(node.left),
            CLikeTranspiler().visit(node.op),
            self.visit(node.right),
        )


class ValueTypeVisitor(ast.NodeVisitor):
    def generic_visit(self, node):
        return "auto"

    def visit_Constant(self, node):
        return value_expr(node)

    def visit_Str(self, node):
        return value_expr(node)

    def visit_Name(self, node):
        if node.id == "True" or node.id == "False":
            return CLikeTranspiler().visit(node)

        var = node.scopes.find(node.id)
        if not var:
            return get_id(node)
        if defined_before(var, node):
            return get_id(node)
        else:
            return self.visit(var.assigned_from.value)

    def visit_NameConstant(self, node):
        return CLikeTranspiler().visit(node)

    def visit_Call(self, node):
        params = [self.visit(arg) for arg in node.args]
        if any(t is None for t in params):
            raise AstNotImplementedError(f"Call({params}) not implemented", node)
        params = ",".join(params)
        return f"{self.visit(node.func)}({params})"

    def visit_Attribute(self, node):
        value_id = get_id(node.value)
        return f"{value_id}.{node.attr}"

    def visit_Assign(self, node):
        if isinstance(node.value, ast.List):
            if len(node.value.elts) > 0:
                val = node.value.elts[0]
                return self.visit(val)
            else:
                target = node.targets[0]
                var = node.scopes.find(get_id(target))
                if hasattr(var, "calls"):
                    first_added_value = var.calls[0].args[0]
                    return value_expr(first_added_value)
                else:
                    return None
        else:
            return self.visit(node.value)


def defined_before(node1, node2):
    """Check if node a has been defined before an other node b"""
    return node1.lineno < node2.lineno


def is_list_assignment(node):
    return isinstance(node.value, ast.List) and isinstance(
        node.targets[0].ctx, ast.Store
    )


def is_list_addition(node):
    """Check if operation is adding something to a list"""
    list_operations = ["append", "extend", "insert"]
    return (
        isinstance(node.func.ctx, ast.Load)
        and hasattr(node.func, "value")
        and isinstance(node.func.value, ast.Name)
        and node.func.attr in list_operations
    )


def is_recursive(fun):
    finder = RecursionFinder()
    finder.visit(fun)
    return finder.recursive


class RecursionFinder(ast.NodeVisitor):
    function_name = None
    recursive = False

    def visit_FunctionDef(self, node):
        self.function_name = node.name
        self.generic_visit(node)

    def visit_Call(self, node):
        self.recursive = (
            isinstance(node.func, ast.Name) and get_id(node.func) == self.function_name
        )
        self.generic_visit(node)
