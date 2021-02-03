import ast
import copy
import re

from common.analysis import get_id


def infer_types(node):
    return InferTypesTransformer().visit(node)


class InferTypesTransformer(ast.NodeTransformer):
    """
    Tries to infer types
    """

    TYPE_DICT = {int: "int", float: "float", str: "str"}

    def __init__(self):
        self.handling_annotation = False

    def visit_NameConstant(self, node):
        t = type(node.value)
        if t in self.TYPE_DICT:
            node.annotation = ast.Name(id=self.TYPE_DICT[t])
        else:
            raise (Exception(f"{t} not found in TYPE_DICT"))

        self.generic_visit(node)
        return node

    def visit_Constant(self, node):
        return self.visit_NameConstant(node)

    def visit_Assign(self, node: ast.Assign) -> ast.AST:
        self.generic_visit(node)

        target = node.targets[0]
        if hasattr(node.value, "annotation"):
            target.annotation = node.value.annotation
        else:
            var = node.scopes.find(get_id(node.value))

            if var and hasattr(var, "annotation"):
                target.annotation = copy.copy(var.annotation)

        return node

    def visit_AugAssign(self, node: ast.AugAssign) -> ast.AST:
        self.generic_visit(node)

        target = node.target
        if hasattr(node.value, "annotation"):
            target.annotation = node.value.annotation

        return node

    def visit_UnaryOp(self, node):
        self.generic_visit(node)

        if isinstance(node.operand, ast.Name):
            operand = node.scopes.find(get_id(node.operand))
        else:
            operand = node.operand

        if hasattr(operand, "annotation"):
            node.annotation = operand.annotation

        return node

    def visit_BinOp(self, node):
        self.generic_visit(node)

        if isinstance(node.left, ast.Name):
            lvar = node.scopes.find(get_id(node.left))
        else:
            lvar = node.left

        if isinstance(node.right, ast.Name):
            rvar = node.scopes.find(get_id(node.right))
        else:
            rvar = node.right

        left = lvar.annotation if lvar and hasattr(lvar, "annotation") else None
        right = rvar.annotation if rvar and hasattr(rvar, "annotation") else None

        if left is None and right is not None:
            node.annotation = right
            return node

        if right is None and left is not None:
            node.annotation = left
            return node

        if right is None and left is None:
            return node

        # Both operands are annotated. Now we have interesting cases
        left_id = get_id(left)
        right_id = get_id(right)
        if left_id == right_id:
            # Exceptions: division operator
            if isinstance(node.op, ast.Div):
                if left_id == "int":
                    node.annotation = ast.Name(id="float")
                    return node
            node.annotation = copy.copy(left)
            return node
        else:
            if (left_id, right_id) in {("int", "float"), ("float", "int")}:
                node.annotation = ast.Name(id="float")
                return node

            raise Exception(f"type error: {left_id} {type(node.op)} {right_id}")

        return node
