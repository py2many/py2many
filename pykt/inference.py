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

KT_TYPE_MAP = {
    bool: "Boolean",
    int: "Int",
    float: "Double",
    bytes: "ByteArray",
    str: "String",
    c_int8: "Byte",
    c_int16: "Short",
    c_int32: "Int",
    c_int64: "Long",
    c_uint8: "UByte",
    c_uint16: "UShort",
    c_uint32: "UInt",
    c_uint64: "ULong",
}

KT_CONTAINER_TYPE_MAP = {
    "List": "Array",
    "Dict": "Dict",
    "Set": "Set",
    "Optional": "Nothing",
}

KT_WIDTH_RANK = {
    "Boolean": 0,
    "Byte": 1,
    "UByte": 2,
    "Short": 3,
    "UShort": 4,
    "Int": 5,
    "UInt": 6,
    "Long": 7,
    "ULong": 8,
    "Float": 9,
    "Double": 10,
}

KT_REVERSE_TYPE_MAP = {v: k for k, v in KT_TYPE_MAP.items()}


class KotlinInference(LanguageInferenceBase):
    TYPE_MAP = KT_TYPE_MAP
    CONTAINER_TYPE_MAP = KT_CONTAINER_TYPE_MAP
    WIDTH_RANK = KT_WIDTH_RANK
    REVERSE_TYPE_MAP = KT_REVERSE_TYPE_MAP


def get_inferred_kotlin_type(node):
    return KotlinInference.get_inferred_language_type(node, "kotlin_annotation")


class InferKotlinTypesTransformer(InferTypesTransformer):
    """Implements kotlin type inference logic as opposed to python type inference logic"""

    def _handle_overflow(self, op, left_id, right_id):
        # Kotlin has special widening rules
        def widen(kotlin_id):
            if kotlin_id in {"Byte", "Short"}:
                return "Int"
            if kotlin_id in {"UByte", "UShort"}:
                return "UInt"
            return kotlin_id

        left_kotlin_id = KotlinInference.map_type(left_id)
        right_kotlin_id = KotlinInference.map_type(right_id)

        left_kotlin_id = widen(left_kotlin_id)
        right_kotlin_id = widen(right_kotlin_id)

        left_id = KotlinInference.REVERSE_TYPE_MAP.get(left_kotlin_id)
        right_id = KotlinInference.REVERSE_TYPE_MAP.get(right_kotlin_id)

        left_kotlin_rank = KT_WIDTH_RANK.get(left_kotlin_id, -1)
        right_kotlin_rank = KT_WIDTH_RANK.get(right_kotlin_id, -1)

        return (
            left_kotlin_id if left_kotlin_rank > right_kotlin_rank else right_kotlin_id
        )

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
            node.kotlin_annotation = get_inferred_kotlin_type(right)
            return node

        if right is None and left is not None:
            node.kotlin_annotation = get_inferred_kotlin_type(left)
            return node

        if right is None and left is None:
            return node

        # Both operands are annotated. Now we have interesting cases
        left_id = get_id(left)
        right_id = get_id(right)

        ret = self._handle_overflow(node.op, left_id, right_id)
        node.kotlin_annotation = ret
        return node


def infer_kotlin_types(node):
    visitor = InferKotlinTypesTransformer()
    visitor.visit(node)
