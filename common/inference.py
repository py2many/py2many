import ast
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
            node.annotation = ast.Name(id=t)
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

        return node

    def visit_AugAssign(self, node: ast.AugAssign) -> ast.AST:
        self.generic_visit(node)

        target = node.target
        if hasattr(node.value, "annotation"):
            target.annotation = node.value.annotation

        return node
