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

NIM_TYPE_MAP = {
    int: "int",
    float: "float64",
    bytes: "openArray[byte]",
    str: "string",
    bool: "bool",
    c_int8: "int8",
    c_int16: "int16",
    c_int32: "int32",
    c_int64: "int64",
    c_uint8: "uint8",
    c_uint16: "uint16",
    c_uint32: "uint32",
    c_uint64: "uint64",
}

NIM_CONTAINER_TYPE_MAP = {
    "List": "seq",
    "Dict": "Table",
    "Set": "set",
    "Optional": "Option",
}

NIM_WIDTH_RANK = {
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
    "float": 9,
}


class NimInference(LanguageInferenceBase):
    TYPE_MAP = NIM_TYPE_MAP
    CONTAINER_TYPE_MAP = NIM_CONTAINER_TYPE_MAP
    WIDTH_RANK = NIM_WIDTH_RANK


def get_inferred_nim_type(node):
    return NimInference.get_inferred_language_type(node, "nim_annotation")


class InferNimTypesTransformer(InferTypesTransformer):
    """Implements nim type inference logic as opposed to python type inference logic"""

    def _handle_overflow(self, op, left_id, right_id):
        return NimInference.handle_overflow(op, left_id, right_id)

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
            node.nim_annotation = get_inferred_nim_type(right)
            return node

        if right is None and left is not None:
            node.nim_annotation = get_inferred_nim_type(left)
            return node

        if right is None and left is None:
            return node

        # Both operands are annotated. Now we have interesting cases
        left_id = get_id(left)
        right_id = get_id(right)

        ret = self._handle_overflow(node.op, left_id, right_id)
        node.nim_annotation = ret
        return node


def infer_nim_types(node):
    visitor = InferNimTypesTransformer()
    visitor.visit(node)
