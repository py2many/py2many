import ast
from ctypes import (
    c_int8,
    c_int16,
    c_int32,
    c_int64,
    c_uint8,
    c_uint16,
    c_uint32,
    c_uint64,
)

from py2many.analysis import get_id
from py2many.inference import InferTypesTransformer, LanguageInferenceBase

GO_TYPE_MAP = {
    bool: "bool",
    int: "int",
    float: "float64",
    bytes: "[]uint8",
    str: "string",
    c_int8: "int8",
    c_int16: "int16",
    c_int32: "int32",
    c_int64: "int64",
    c_uint8: "uint8",
    c_uint16: "uint16",
    c_uint32: "uint32",
    c_uint64: "uint64",
}

GO_CONTAINER_TYPE_MAP = {"List": "[]", "Dict": None, "Set": None, "Optional": "nil"}

GO_WIDTH_RANK = {
    "bool": 0,
    "int8": 1,
    "uint8": 2,
    "int16": 3,
    "uint16": 4,
    "int32": 5,
    "uint32": 6,
    "int64": 7,
    "uint64": 8,
    "float32": 9,
    "float64": 10,
}


class GoInference(LanguageInferenceBase):
    TYPE_MAP = GO_TYPE_MAP
    CONTAINER_TYPE_MAP = GO_CONTAINER_TYPE_MAP
    WIDTH_RANK = GO_WIDTH_RANK


def get_inferred_go_type(node):
    return GoInference.get_inferred_language_type(node, "go_annotation")


class InferGoTypesTransformer(InferTypesTransformer):
    """Implements go type inference logic as opposed to python type inference logic"""

    def _handle_overflow(self, op, left_id, right_id):
        return GoInference.handle_overflow(op, left_id, right_id)

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
            node.go_annotation = get_inferred_go_type(right)
            return node

        if right is None and left is not None:
            node.go_annotation = get_inferred_go_type(left)
            return node

        if right is None and left is None:
            return node

        # Both operands are annotated. Now we have interesting cases
        left_id = get_id(left)
        right_id = get_id(right)

        ret = self._handle_overflow(node.op, left_id, right_id)
        node.go_annotation = ret
        return node


def infer_go_types(node):
    visitor = InferGoTypesTransformer()
    visitor.visit(node)
