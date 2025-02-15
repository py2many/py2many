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

JL_TYPE_MAP = {
    int: "Int64",
    float: "Float64",
    bytes: "Vector{UInt8}",
    str: "String",
    bool: "Bool",
    c_int8: "Int8",
    c_int16: "Int16",
    c_int32: "Int32",
    c_int64: "Int64",
    c_uint8: "UInt8",
    c_uint16: "UInt16",
    c_uint32: "UInt32",
    c_uint64: "UInt64",
}

JL_CONTAINER_TYPE_MAP = {
    "List": "Vector",
    "Dict": "Dict",
    "Set": "Set",
    "Optional": "Union{Nothing}",
}

JL_WIDTH_RANK = {
    "Bool": 0,
    "Int8": 1,
    "UInt8": 2,
    "Int16": 3,
    "UInt16": 4,
    "Int32": 5,
    "UInt32": 6,
    "Int64": 7,
    "UInt64": 8,
    "Float32": 9,
    "Float64": 10,
}


class JuliaInference(LanguageInferenceBase):
    TYPE_MAP = JL_TYPE_MAP
    CONTAINER_TYPE_MAP = JL_CONTAINER_TYPE_MAP
    WIDTH_RANK = JL_WIDTH_RANK


def get_inferred_julia_type(node):
    return JuliaInference.get_inferred_language_type(node, "julia_annotation")


class InferJuliaTypesTransformer(InferTypesTransformer):
    """Implements julia type inference logic as opposed to python type inference logic"""

    def _handle_overflow(self, op, left_id, right_id):
        return JuliaInference.handle_overflow(op, left_id, right_id)

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
            node.julia_annotation = get_inferred_julia_type(right)
            return node

        if right is None and left is not None:
            node.julia_annotation = get_inferred_julia_type(left)
            return node

        if right is None and left is None:
            return node

        # Both operands are annotated. Now we have interesting cases
        left_id = get_id(left)
        right_id = get_id(right)

        ret = self._handle_overflow(node.op, left_id, right_id)
        node.julia_annotation = ret
        return node


def infer_julia_types(node):
    visitor = InferJuliaTypesTransformer()
    visitor.visit(node)
