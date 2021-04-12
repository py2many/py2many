# Trace object types that are inserted into Python list.
import ast
from py2many.analysis import get_id
from py2many.tracer import is_list, ValueExpressionVisitor, ValueTypeVisitor
from py14.clike import CLikeTranspiler


def decltype(node):
    """Create C++ decltype statement"""
    if is_list(node):
        return "std::vector<decltype({0})>".format(value_type(node))
    else:
        return "decltype({0})".format(value_type(node))


def value_expr(node):
    """
    Follow all assignments down the rabbit hole in order to find
    the value expression of a name.
    The boundary is set to the current scope.
    """
    return Py14ValueExpressionVisitor().visit(node)


def value_type(node):
    """
    Guess the value type of a node based on the manipulations or assignments
    in the current scope.
    Special case: If node is a container like a list the value type inside the
    list is returned not the list type itself.
    """
    return Py14ValueTypeVisitor().visit(node)


class Py14ValueExpressionVisitor(ValueExpressionVisitor):
    def visit_Name(self, node):
        var = node.scopes.find(get_id(node))

        if not var:  # TODO why no scopes found for node id?
            return get_id(node)

        if isinstance(var.assigned_from, ast.For):
            it = var.assigned_from.iter
            return "std::declval<typename decltype({0})::value_type>()".format(
                self.visit(it)
            )
        elif isinstance(var.assigned_from, ast.FunctionDef):
            return get_id(var)
        else:
            return self.visit(var.assigned_from.value)


class Py14ValueTypeVisitor(ValueTypeVisitor):
    def visit_NameConstant(self, node):
        return CLikeTranspiler().visit(node)

    def visit_Constant(self, node):
        return CLikeTranspiler().visit(node)
