"""
Trace object types that are inserted into Python list.
"""
import ast
from context import add_variable_context
from clike import CLikeTranspiler
from generic.multidispatch import multifunction


def decltype(node):
    """Create C++ decltype statement"""
    if is_list(node):
        return "std::vector<decltype({0})>".format(value_type(node))
    else:
        return "decltype({0})".format(value_type(node))


def is_list(node):
    """Check if a node was assigned as a list"""
    if isinstance(node, ast.List):
        return True
    elif isinstance(node, ast.Assign):
        return is_list(node.value)
    elif isinstance(node, ast.Name):
        var = node.scopes.find(node.id)
        return is_list(var.assigned_from.value)
    else:
        return False


@multifunction(ast.Num)
def value_expr(node):
    """
    Follow all assignments down the rabbit hole in order to find
    the value expression of a name.
    The boundary is set to the current scope.
    """
    return str(node.n)

@value_expr.when(ast.Str)
def value_expr(node):
    return node.s

@value_expr.when(ast.Name)
def value_expr(node):
    var = node.scopes.find(node.id)
    if isinstance(var.assigned_from, ast.For):
        iter = var.assigned_from.iter
        return "declval<decltype({0})::value_type>()".format(value_expr(iter))
    elif isinstance(var.assigned_from, ast.FunctionDef):
        return var.id
    else:
        return value_expr(var.assigned_from.value)

@value_expr.when(ast.Call)
def value_expr(node):
    params = ",".join([value_expr(arg) for arg in node.args])
    return "{0}({1})".format(node.func.id, params)

@value_expr.when(ast.Assign)
def value_expr(node):
        return value_expr(node.value)

@value_expr.when(ast.BinOp)
def value_expr(node):
    return "{0} {1} {2}".format(value_expr(node.left),
                                CLikeTranspiler().visit(node.op),
                                value_expr(node.right))


@multifunction(ast.Num)
def value_type(node):
    """
    Guess the value type of a node based on the manipulations or assignments
    in the current scope.
    Special case: If node is a container like a list the value type inside the
    list is returned not the list type itself.
    """
    return value_expr(node)


@value_type.when(ast.Str)
def value_type(node):
    return value_expr(node)


@value_type.when(ast.Assign)
def value_type(node):
    if isinstance(node.value, ast.List):
        if len(node.value.elts) > 0:
            val = node.value.elts[0]
            return value_type(val)
        else:
            target = node.targets[0]
            var = node.scopes.find(target.id)
            first_added_value = var.calls[0].args[0]
            return value_expr(first_added_value)
    else:
        return value_type(node.value)


@value_type.when(ast.Name)
def value_type(node):
    var = node.scopes.find(node.id)
    if defined_before(var, node):
        return node.id
    else:
        return value_type(var.assigned_from.value)


@value_type.when(ast.Call)
def value_type(node):
    params = ",".join([value_type(arg) for arg in node.args])
    return "{0}({1})".format(node.func.id, params)


def defined_before(node1, node2):
    """Check if node a has been defined before an other node b"""
    return node1.lineno < node2.lineno


def is_list_assignment(node):
    return (isinstance(node.value, ast.List) and
            isinstance(node.targets[0].ctx, ast.Store))


def is_list_addition(node):
    """Check if operation is adding something to a list"""
    list_operations = ["append", "extend", "insert"]
    return (isinstance(node.func.ctx, ast.Load) and
            hasattr(node.func, "value") and
            isinstance(node.func.value, ast.Name) and
            node.func.attr in list_operations)
