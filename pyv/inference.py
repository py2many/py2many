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
from typing import Dict, List

from py2many.analysis import get_id
from py2many.inference import InferTypesTransformer, LanguageInferenceBase

V_TYPE_MAP: Dict[type, str] = {
    int: "int",
    float: "f64",
    bytes: "[]byte",
    str: "string",
    bool: "bool",
    list: "[]Any",
    List: "[]Any",
    c_int8: "i8",
    c_int16: "i16",
    c_int32: "int",
    c_int64: "i64",
    c_uint8: "byte",
    c_uint16: "u16",
    c_uint32: "u32",
    c_uint64: "u64",
}

V_CONTAINER_TYPE_MAP = {
    "List": "[]",
    "list": "[]",
    "Dict": "map",
    "dict": "map",
    "Set": "set",
    "set": "set",
    "Optional": "?",
}

V_WIDTH_RANK = {
    "bool": 0,
    "i8": 1,
    "byte": 2,
    "i16": 3,
    "u16": 4,
    "int": 5,
    "u32": 6,
    "i64": 7,
    "u64": 8,
    "f32": 9,
    "f64": 10,
}


class VInference(LanguageInferenceBase):
    TYPE_MAP = V_TYPE_MAP
    CONTAINER_TYPE_MAP = V_CONTAINER_TYPE_MAP
    WIDTH_RANK = V_WIDTH_RANK


def get_inferred_v_type(node):
    return VInference.get_inferred_language_type(node, "v_annotation")


class InferVTypesTransformer(InferTypesTransformer):
    """Implements v type inference logic as opposed to python type inference logic"""

    def _handle_overflow(self, op, left_id, right_id):
        return VInference.handle_overflow(op, left_id, right_id)

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
            node.v_annotation = get_inferred_v_type(right)
            return node

        if right is None and left is not None:
            node.v_annotation = get_inferred_v_type(left)
            return node

        if right is None and left is None:
            return node

        # Both operands are annotated. Now we have interesting cases
        left_id = get_id(left)
        right_id = get_id(right)

        ret = self._handle_overflow(node.op, left_id, right_id)
        node.v_annotation = ret
        return node


def infer_v_types(node):
    visitor = InferVTypesTransformer()
    visitor.visit(node)
