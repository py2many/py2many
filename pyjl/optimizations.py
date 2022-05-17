
import ast
from typing import Any

from py2many.ast_helpers import get_id


class AlgebraicSimplification(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()
        self._optimize = False

    def visit_Subscript(self, node: ast.Subscript) -> Any:
        self._generic_optimize_visit(node)
        return node

    def visit_Call(self, node: ast.Call) -> Any:
        # For now, just optimize range function calls
        if get_id(node.func) == "range":
            self._generic_optimize_visit(node)
        else:
            self.generic_visit(node)
        return node

    def _generic_optimize_visit(self, node):
        is_nested = self._optimize
        if not is_nested:
            self._optimize = True
            self.generic_visit(node)
            self._optimize = False
        else:
            self.generic_visit(node)

    def visit_BinOp(self, node: ast.BinOp) -> Any:
        self.generic_visit(node)
        if self._optimize:
            if isinstance(node.left, ast.BinOp) and \
                    isinstance(node.right, ast.Constant):
                if isinstance(node.left.right, ast.Constant) and \
                        isinstance(node.left.right.value, int):
                    # Deal with subtraction and addition
                    left_op = node.left.op
                    if isinstance(node.op, ast.Sub):
                        if isinstance(left_op, ast.Sub):
                            node.left.right.value += node.right.value
                        elif isinstance(left_op, ast.Add):
                            node.left.right.value = node.left.right.value - node.right.value
                        if node.left.right.value == 0:
                            return node.left.left
                        return node.left
                    if isinstance(node.op, ast.Add):
                        if isinstance(left_op, ast.Sub):
                            node.left.right.value = -node.left.right.value + node.right.value
                        elif isinstance(left_op, ast.Add):
                            node.left.right.value += node.right.value
                        if node.left.right.value == 0:
                            return node.left.left
                        return node.left
            if isinstance(node.left, ast.UnaryOp) and \
                    isinstance(node.right, ast.Constant):
                if isinstance(node.left.op, ast.USub) and \
                        isinstance(node.left.operand, ast.Constant):
                    return ast.Constant(
                        value = (-node.left.operand.value + node.right.value))
            if isinstance(node.left, ast.Constant) \
                    and isinstance(node.right, ast.Constant):
                if isinstance(node.op, ast.Sub):
                    return ast.Constant(node.left.value - node.right.value)
                elif isinstance(node.op, ast.Add):
                    return ast.Constant(node.left.value + node.right.value)

        return node
