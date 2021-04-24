import ast
from py2many.inference import get_inferred_type

from ctypes import c_int8, c_int16, c_int32, c_int64
from ctypes import c_uint8, c_uint16, c_uint32, c_uint64

from py2many.analysis import get_id

RUST_TYPE_MAP = {
    "int": "i32",
    "float": "f32",
    "bytes": "&[u8]",
    "str": "&str",
    "bool": "bool",
    "c_int8": "i8",
    "c_int16": "i16",
    "c_int32": "i32",
    "c_int64": "i64",
    "c_uint8": "u8",
    "c_uint16": "u16",
    "c_uint32": "u32",
    "c_uint64": "u64",
}


RUST_WIDTH_RANK = {
    "i8": 0,
    "u8": 1,
    "i16": 2,
    "u16": 3,
    "i32": 4,
    "u32": 5,
    "i64": 6,
    "u64": 7,
    "f32": 8,
    "f64": 9,
}


def infer_rust_types(node):
    visitor = InferRustTypesTransformer()
    visitor.visit(node)


def map_type(typename):
    if typename in RUST_TYPE_MAP:
        return RUST_TYPE_MAP[typename]
    return typename


def get_inferred_rust_type(node):
    if isinstance(node, ast.Name):
        if not hasattr(node, "scopes"):
            return None
        definition = node.scopes.find(get_id(node))
        # Prevent infinite recursion
        if definition != node:
            return get_inferred_rust_type(definition)
    if hasattr(node, "rust_annotation"):
        return node.rust_annotation
    python_type = get_inferred_type(node)
    return map_type(get_id(python_type))


class InferRustTypesTransformer(ast.NodeTransformer):
    """Implements rust type inference logic as opposed to python type inference logic"""

    FIXED_WIDTH_INTS = {
        c_int8,
        c_int16,
        c_int32,
        c_int64,
        c_uint8,
        c_uint16,
        c_uint32,
        c_uint64,
    }
    FIXED_WIDTH_INTS_NAME_LIST = [
        "c_int8",
        "c_int16",
        "c_int32",
        "c_int64",
        "c_uint8",
        "c_uint16",
        "c_uint32",
        "c_uint64",
    ]
    FIXED_WIDTH_INTS_NAME = set(FIXED_WIDTH_INTS_NAME_LIST)

    def __init__(self):
        super().__init__()

    def _handle_overflow(self, op, left_id, right_id):
        left_rust_id = map_type(left_id)
        right_rust_id = map_type(right_id)

        left_rust_rank = RUST_WIDTH_RANK.get(left_rust_id, -1)
        right_rust_rank = RUST_WIDTH_RANK.get(right_rust_id, -1)

        return left_id if left_rust_rank > right_rust_rank else right_id

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
            node.rust_annotation = map_type(get_id(right))
            return node

        if right is None and left is not None:
            node.rust_annotation = map_type(get_id(left))
            return node

        if right is None and left is None:
            return node

        # Both operands are annotated. Now we have interesting cases
        left_id = get_id(left)
        right_id = get_id(right)

        if (
            left_id in self.FIXED_WIDTH_INTS_NAME
            and right_id in self.FIXED_WIDTH_INTS_NAME
        ):
            ret = self._handle_overflow(node.op, left_id, right_id)
            node.rust_annotation = map_type(ret)
            return node
        if left_id == right_id:
            node.annotation = left
            node.rust_annotation = map_type(left_id)
            return node
        else:
            if left_id in self.FIXED_WIDTH_INTS_NAME:
                left_id = "int"
            if right_id in self.FIXED_WIDTH_INTS_NAME:
                right_id = "int"
            if (left_id, right_id) in {("int", "float"), ("float", "int")}:
                node.rust_annotation = map_type("float")
                return node

            raise Exception(f"type error: {left_id} {type(node.op)} {right_id}")
