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

ZIG_TYPE_MAP = {
    int: "i32",
    float: "f64",
    bytes: "[]u8",
    bytearray: "[]u8",
    str: "[]const u8",
    bool: "bool",
    c_int8: "i8",
    c_int16: "i16",
    c_int32: "i32",
    c_int64: "i64",
    c_uint8: "u8",
    c_uint16: "u16",
    c_uint32: "u32",
    c_uint64: "u64",
}

ZIG_CONTAINER_TYPE_MAP = {
    "List": "pylib.AutoArrayList",
    "Dict": "pylib.AutoMap",
    "Set": "pylib.AutoSet",
    "Optional": "Optional",
}

ZIG_WIDTH_RANK = {
    "bool": 0,
    "i8": 1,
    "u8": 2,
    "i16": 3,
    "u16": 4,
    "i32": 5,
    "u32": 6,
    "i64": 7,
    "u64": 8,
    "f32": 9,
    "f64": 10,
}


class ZigInference(LanguageInferenceBase):
    TYPE_MAP = ZIG_TYPE_MAP
    CONTAINER_TYPE_MAP = ZIG_CONTAINER_TYPE_MAP
    WIDTH_RANK = ZIG_WIDTH_RANK


def get_inferred_zig_type(node):
    return ZigInference.get_inferred_language_type(node, "zig_annotation")


class InferZigTypesTransformer(InferTypesTransformer):
    """Implements zig type inference logic as opposed to python type inference logic"""

    def _handle_overflow(self, op, left_id, right_id):
        return ZigInference.handle_overflow(op, left_id, right_id)

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
            node.zig_annotation = get_inferred_zig_type(right)
            return node

        if right is None and left is not None:
            node.zig_annotation = get_inferred_zig_type(left)
            return node

        if right is None and left is None:
            return node

        # Both operands are annotated. Now we have interesting cases
        left_id = get_id(left)
        right_id = get_id(right)

        ret = self._handle_overflow(node.op, left_id, right_id)
        node.zig_annotation = ret
        return node


def infer_zig_types(node):
    visitor = InferZigTypesTransformer()
    visitor.visit(node)
