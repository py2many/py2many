"""
Trace object types that are inserted into Python list.
"""
import ast
from context import add_variable_context



def determine_value(node, position=None):
    if not position:
        position = node

    if isinstance(node, ast.Num):
        return str(node.n)
    elif isinstance(node, ast.Str):
        return node.s
    elif isinstance(node, ast.Name):
        var = [d for d in node.scope.vars if d.id == node.id][0]
        if defined_before(var, position):
            return node.id
        else:
            return determine_value(var.assigned_from.value, position)


def determine_type(node, position=None):
    """Find out type of a given node from the standpoint from position"""
    if not position:
        position = node

    if isinstance(node, ast.Num):
        return "decltype({0})".format(node.n)
    elif isinstance(node, ast.Str):
        return "std::string"
    elif isinstance(node, ast.Name):
        var = [d for d in node.scope.vars if d.id == node.id][0]
        if defined_before(var, position):
            return "decltype({0})".format(node.id)
        else:
            return determine_type(var.assigned_from.value, position)
    elif isinstance(node, ast.Call):
        params = ",".join([determine_value(arg) for arg in node.args])
        # if possible params should now be values not declvals
        return "decltype({0}({1}))".format(node.func.id, params)
    else:
        raise ValueError("No list type known for node")
    pass


class ListTracer(ast.NodeTransformer):
    """Adds information about which types are added to a list"""

    def __init__(self, list_name):
        super(ListTracer, self).__init__()
        self.list_name = list_name
        self.function_calls = []
        self.list_calls = []
        self.local_vars = []

    def visit_Call(self, node):
        import pytest; pytest.set_trace()
        if is_list_addition(node) and node.func.value.id == self.list_name:
            arg = node.args[0]
            if isinstance(arg, ast.Num):
                print("decltype({0})".format(arg.n))
            else:
                definition = self.find_definition(arg)
                if defined_before(definition, arg):
                    pass
                else:
                    pass
            self.list_calls.append(node)
        return node

    def visit_Assign(self, node):
        if is_list_assignment(node):
            self.list_vars.append(node)
        else:
            self.local_vars.append(node)
        return node

    def visit_FunctionDef(self, node):
        for arg in node.args.args:
            self.local_vars.append(arg)
        self.generic_visit(node)
        node.function_calls = self.function_calls
        node.local_vars = self.local_vars
        node.list_vars = self.list_vars
        return node

    def find_definition(self, node):
        for var in self.local_vars:
            if var.id == node.id:
                return var


def defined_before(a, b):
    """Check if node a has been defined before an other node b"""
    return a.lineno < b.lineno


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
