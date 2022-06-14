import ast
from typing import Any

from py2many.ast_helpers import get_id


class JuliaIndexingRewriter(ast.NodeTransformer):

    def __init__(self) -> None:
        super().__init__()

    def visit_Call(self, node: ast.Call) -> Any:
        self.generic_visit(node)
        call_id = get_id(node.func)
        if (call_id == "range" or call_id == "xrange"):
            # decrement stop
            if len(node.args) == 1:
                node.args[0] = self._do_bin_op(node.args[0], ast.Sub(), 1,
                    node.lineno, node.col_offset)
            elif len(node.args) > 1:
                node.args[1] = self._do_bin_op(node.args[1], ast.Sub(), 1,
                    node.lineno, node.col_offset)
            if len(node.args) == 3:
                # Cover reverse lookup
                if isinstance(node.args[2], ast.UnaryOp) and \
                        isinstance(node.args[2].op, ast.USub):
                    node.args[0], node.args[1] = node.args[1], node.args[0]
        return node

    def _do_bin_op(self, node, op, val, lineno, col_offset):
        left = node
        left.annotation = ast.Name(id="int")
        return ast.BinOp(
                    left = left,
                    op = op,
                    right = ast.Constant(
                        value = val, 
                        annotation = ast.Name(id= "int"),
                        scopes = node.scopes),
                    lineno = lineno,
                    col_offset = col_offset,
                    scopes = node.scopes
                )