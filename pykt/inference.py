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
from py2many.clike import class_for_typename
from py2many.exceptions import AstUnrecognisedBinOp
from py2many.inference import InferTypesTransformer, get_inferred_type

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

REVERSE_KT_TYPE_MAP = {v: k for k, v in KT_TYPE_MAP.items()}

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


def infer_kotlin_types(node):
    visitor = InferKotlinTypesTransformer()
    visitor.visit(node)


def map_type(typename):
    typeclass = class_for_typename(typename, None)
    if typeclass in KT_TYPE_MAP:
        return KT_TYPE_MAP[typeclass]
    return typename


def get_inferred_kotlin_type(node):
    if isinstance(node, ast.Call):
        fname = get_id(node.func)
        if fname in {"max", "min", "floor"}:
            return "float64"
    if isinstance(node, ast.Name):
        if not hasattr(node, "scopes"):
            return None
        definition = node.scopes.find(get_id(node))
        # Prevent infinite recursion
        if definition != node:
            return get_inferred_kotlin_type(definition)
    if hasattr(node, "kotlin_annotation"):
        return node.kotlin_annotation
    python_type = get_inferred_type(node)
    return map_type(get_id(python_type))


# Copy pasta from rust. Double check for correctness
class InferKotlinTypesTransformer(ast.NodeTransformer):
    """Implements kotlin type inference logic as opposed to python type inference logic"""

    FIXED_WIDTH_INTS = InferTypesTransformer.FIXED_WIDTH_INTS
    FIXED_WIDTH_INTS_NAME_LIST = InferTypesTransformer.FIXED_WIDTH_INTS_NAME
    FIXED_WIDTH_INTS_NAME = InferTypesTransformer.FIXED_WIDTH_INTS_NAME_LIST

    def _handle_overflow(self, op, left_id, right_id):
        left_kotlin_id = map_type(left_id)
        right_kotlin_id = map_type(right_id)

        # Derived this by messing around with the compiler
        def widen(kotlin_id):
            if kotlin_id in {"Byte", "Short"}:
                return "Int"
            if kotlin_id in {"UByte", "UShort"}:
                return "UInt"
            return kotlin_id

        left_kotlin_id = widen(left_kotlin_id)
        right_kotlin_id = widen(right_kotlin_id)

        left_id = REVERSE_KT_TYPE_MAP.get(left_kotlin_id)
        right_id = REVERSE_KT_TYPE_MAP.get(right_kotlin_id)

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

        # Special case int op int = int, where op != Div
        if (
            left_id == right_id
            and left_id == "int"
            and not isinstance(node.op, ast.Div)
        ):
            node.annotation = left
            node.kotlin_annotation = map_type(left_id)
            return node

        if left_id == "int":
            left_id = "c_int32"
        if right_id == "int":
            right_id = "c_int32"

        if (
            left_id in self.FIXED_WIDTH_INTS_NAME
            and right_id in self.FIXED_WIDTH_INTS_NAME
        ):
            ret = self._handle_overflow(node.op, left_id, right_id)
            node.kotlin_annotation = ret
            return node
        if left_id == right_id:
            node.annotation = left
            node.kotlin_annotation = map_type(left_id)
            return node
        else:
            if left_id in self.FIXED_WIDTH_INTS_NAME:
                left_id = "int"
            if right_id in self.FIXED_WIDTH_INTS_NAME:
                right_id = "int"
            if (left_id, right_id) in {("int", "float"), ("float", "int")}:
                node.kotlin_annotation = map_type("float")
                return node

            raise AstUnrecognisedBinOp(left_id, right_id, node)
