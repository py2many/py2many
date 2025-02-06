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
    "List": "ArrayList",
    "Dict": "HashMap",
    "Set": "HashSet",
    "Optional": "Optional",
}


ZIG_WIDTH_RANK = {
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


def infer_zig_types(node):
    visitor = InferZigTypesTransformer()
    visitor.visit(node)


def map_type(typename):
    typeclass = class_for_typename(typename, None)
    if typeclass in ZIG_TYPE_MAP:
        return ZIG_TYPE_MAP[typeclass]
    return typename


def get_inferred_zig_type(node):
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
            return get_inferred_zig_type(definition)
    if hasattr(node, "zig_annotation"):
        return node.zig_annotation
    python_type = get_inferred_type(node)
    return map_type(get_id(python_type))


# Copy pasta from rust. Double check for correctness
class InferZigTypesTransformer(ast.NodeTransformer):
    """Implements zig type inference logic as opposed to python type inference logic"""

    FIXED_WIDTH_INTS = InferTypesTransformer.FIXED_WIDTH_INTS
    FIXED_WIDTH_INTS_NAME_LIST = InferTypesTransformer.FIXED_WIDTH_INTS_NAME
    FIXED_WIDTH_INTS_NAME = InferTypesTransformer.FIXED_WIDTH_INTS_NAME_LIST

    def _handle_overflow(self, op, left_id, right_id):
        left_zig_id = map_type(left_id)
        right_zig_id = map_type(right_id)

        left_zig_rank = ZIG_WIDTH_RANK.get(left_zig_id, -1)
        right_zig_rank = ZIG_WIDTH_RANK.get(right_zig_id, -1)

        return left_zig_id if left_zig_rank > right_zig_rank else right_zig_id

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
            node.zig_annotation = ret
            return node
        if left_id == right_id:
            node.annotation = left
            node.zig_annotation = map_type(left_id)
            return node
        else:
            if left_id in self.FIXED_WIDTH_INTS_NAME:
                left_id = "int"
            if right_id in self.FIXED_WIDTH_INTS_NAME:
                right_id = "int"
            if (left_id, right_id) in {("int", "float"), ("float", "int")}:
                node.zig_annotation = map_type("float")
                return node

            raise AstUnrecognisedBinOp(left_id, right_id, node)
