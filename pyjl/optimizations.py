import ast
import re
from typing import Any

from py2many.ast_helpers import get_id
from pyjl.global_vars import FLAG_DEFAULTS, USE_GLOBAL_CONSTANTS


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
        self.visit(node.left)
        if self._optimize:
            if isinstance(node.left, ast.BinOp) and isinstance(
                node.right, ast.Constant
            ):
                if isinstance(node.left.right, ast.Constant) and isinstance(
                    node.left.right.value, int
                ):
                    # Deal with subtraction and addition
                    left_op = node.left.op
                    if isinstance(node.op, ast.Sub):
                        if isinstance(left_op, ast.Sub):
                            node.left.right.value += node.right.value
                        elif isinstance(left_op, ast.Add):
                            node.left.right.value = (
                                node.left.right.value - node.right.value
                            )
                        if node.left.right.value == 0:
                            return node.left.left
                        return node.left
                    if isinstance(node.op, ast.Add):
                        if isinstance(left_op, ast.Sub):
                            node.left.right.value = (
                                -node.left.right.value + node.right.value
                            )
                        elif isinstance(left_op, ast.Add):
                            node.left.right.value += node.right.value
                        if node.left.right.value == 0:
                            return node.left.left
                        return node.left
            if isinstance(node.left, ast.UnaryOp) and isinstance(
                node.right, ast.Constant
            ):
                if isinstance(node.left.op, ast.USub) and isinstance(
                    node.left.operand, ast.Constant
                ):
                    return ast.Constant(
                        value=(-node.left.operand.value + node.right.value),
                        scopes=node.left.scopes,
                    )
            if isinstance(node.left, ast.Constant) and isinstance(
                node.right, ast.Constant
            ):
                if isinstance(node.op, ast.Sub):
                    return ast.Constant(
                        value=node.left.value - node.right.value,
                        scopes=node.left.scopes,
                    )
                elif isinstance(node.op, ast.Add):
                    return ast.Constant(
                        value=node.left.value + node.right.value,
                        scopes=node.left.scopes,
                    )
        self.visit(node.right)
        return node

class OperationOptimizer(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()

    def visit_Call(self, node: ast.Call) -> Any:
        # Visit call node, as JuliaAugAssignRewirter translates
        # augmented assignments into the corresponding Julia
        # functions
        primitive_type = lambda n: \
            re.match(r"^int|^float|^str", 
            ast.unparse(getattr(node.scopes.find(get_id(n)), "annotation", ast.Name("")))) is not None
        if isinstance(node.func, ast.Name) and \
                get_id(node.func) == "append!" and \
                isinstance(node.args[1], ast.List) and \
                len(node.args[1].elts) == 1 and \
                primitive_type(node.args[1].elts[0]):
            node.func.id = "push!"
            node.args[1] = node.args[1].elts[0]
        return node

class PerformanceOptimizations(ast.NodeTransformer):
    def __init__(self) -> None:
        super().__init__()
        self._use_global_constants = False
    
    def visit_Module(self, node: ast.Module) -> Any:
        self._use_global_constants = getattr(node, USE_GLOBAL_CONSTANTS, 
            FLAG_DEFAULTS[USE_GLOBAL_CONSTANTS])
        self.generic_visit(node)
        return node

    def visit_Assign(self, node: ast.Assign) -> Any:
        self.generic_visit(node)
        target = get_id(node.targets[0])
        if self._use_global_constants:
            scopes = getattr(node, "scopes", None)
            if scopes and isinstance(scopes[-1], ast.Module) and \
                    len(node.targets) == 1 and \
                    target not in scopes[-1].mutable_vars:
                node.use_constant = True
        return node
    