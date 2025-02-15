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
from typing import Callable

from py2many.analysis import get_id
from py2many.inference import InferTypesTransformer, LanguageInferenceBase

SMT_TYPE_MAP = {
    int: "Int",
    float: "Float64",
    bytes: "Array Int Int",  # SMT uses Array type with integer indices
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
    Callable: "FuncType",
}

SMT_CONTAINER_TYPE_MAP = {
    "List": "Array Int",  # Array with integer indices
    "Dict": "Array",  # General Array type
    "Set": "Array Bool",  # Array with boolean values for set membership
    "Optional": "Option",
}

SMT_WIDTH_RANK = {
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
    "Float": 9,
}


class SmtInference(LanguageInferenceBase):
    TYPE_MAP = SMT_TYPE_MAP
    CONTAINER_TYPE_MAP = SMT_CONTAINER_TYPE_MAP
    WIDTH_RANK = SMT_WIDTH_RANK

    @classmethod
    def map_type(cls, typename):
        mapped = super().map_type(typename)
        # Special handling for array types in SMT
        if mapped.startswith("Array"):
            parts = mapped.split()
            if len(parts) == 2:  # List case
                return f"(Array Int {parts[1]})"
            if len(parts) == 3:  # Bytes/bytearray case
                return f"(Array {parts[1]} {parts[2]})"
        return mapped


def get_inferred_smt_type(node):
    return SmtInference.get_inferred_language_type(node, "smt_annotation")


class InferSmtTypesTransformer(InferTypesTransformer):
    """Implements smt type inference logic as opposed to python type inference logic"""

    def _handle_overflow(self, op, left_id, right_id):
        return SmtInference.handle_overflow(op, left_id, right_id)

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
            node.smt_annotation = get_inferred_smt_type(right)
            return node

        if right is None and left is not None:
            node.smt_annotation = get_inferred_smt_type(left)
            return node

        if right is None and left is None:
            return node

        # Both operands are annotated. Now we have interesting cases
        left_id = get_id(left)
        right_id = get_id(right)

        ret = self._handle_overflow(node.op, left_id, right_id)
        node.smt_annotation = ret
        return node


def infer_smt_types(node: ast.AST):
    visitor = InferSmtTypesTransformer()
    visitor.visit(node)
