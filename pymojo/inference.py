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

MOJO_TYPE_MAP = {
    int: "Int",
    float: "Float64",
    bytes: "SIMD[DType.uint8]",
    bytearray: "SIMD[DType.uint8]",
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

MOJO_CONTAINER_TYPE_MAP = {
    "List": "List",
    "Dict": "Dict",
    "Set": "Set",
    "Optional": "Optional",
}

MOJO_WIDTH_RANK = {
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


def infer_mojo_types(node):
    visitor = InferMojoTypesTransformer()
    visitor.visit(node)


def map_type(typename):
    typeclass = class_for_typename(typename, None)
    if typeclass in MOJO_TYPE_MAP:
        return MOJO_TYPE_MAP[typeclass]
    return typename


def get_inferred_mojo_type(node):
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
            return get_inferred_mojo_type(definition)
    if hasattr(node, "mojo_annotation"):
        return node.mojo_annotation
    python_type = get_inferred_type(node)
    return map_type(get_id(python_type))


# Copy pasta from rust. Double check for correctness
class InferMojoTypesTransformer(ast.NodeTransformer):
    """Implements mojo type inference logic as opposed to python type inference logic"""

    FIXED_WIDTH_INTS = InferTypesTransformer.FIXED_WIDTH_INTS
    FIXED_WIDTH_INTS_NAME_LIST = InferTypesTransformer.FIXED_WIDTH_INTS_NAME
    FIXED_WIDTH_INTS_NAME = InferTypesTransformer.FIXED_WIDTH_INTS_NAME_LIST

    def _handle_overflow(self, op, left_id, right_id):
        left_mojo_id = map_type(left_id)
        right_mojo_id = map_type(right_id)

        left_mojo_rank = MOJO_WIDTH_RANK.get(left_mojo_id, -1)
        right_mojo_rank = MOJO_WIDTH_RANK.get(right_mojo_id, -1)

        return left_mojo_id if left_mojo_rank > right_mojo_rank else right_mojo_id

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
            node.mojo_annotation = get_inferred_mojo_type(right)
            return node

        if right is None and left is not None:
            node.mojo_annotation = get_inferred_mojo_type(left)
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
            node.go_annotation = map_type(left_id)
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
            node.mojo_annotation = ret
            return node
        if left_id == right_id:
            node.annotation = left
            node.mojo_annotation = map_type(left_id)
            return node
        else:
            if left_id in self.FIXED_WIDTH_INTS_NAME:
                left_id = "int"
            if right_id in self.FIXED_WIDTH_INTS_NAME:
                right_id = "int"
            if (left_id, right_id) in {("int", "float"), ("float", "int")}:
                node.mojo_annotation = map_type("float")
                return node

            raise AstUnrecognisedBinOp(left_id, right_id, node)
