import ast

from py2many.ast_helpers import get_id
from py2many.tracer import is_list


class JuliaMethodCallRewriter(ast.NodeTransformer):
    def visit_Call(self, node):
        fname = node.func
        if isinstance(fname, ast.Attribute):
            if is_list(node.func.value) and fname.attr == "append":
                new_func_name = "push!"
            else:
                new_func_name = fname.attr
            if get_id(fname.value):
                node0 = ast.Name(id=get_id(fname.value), lineno=node.lineno)
            else:
                node0 = fname.value
            node.args = [node0] + node.args
            node.func = ast.Name(id=new_func_name, lineno=node.lineno, ctx=fname.ctx)
        return node
