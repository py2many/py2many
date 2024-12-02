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
from typing import Dict

from py2many.analysis import get_id
from py2many.clike import class_for_typename
from py2many.exceptions import AstUnrecognisedBinOp
from py2many.inference import InferTypesTransformer, get_inferred_type

V_TYPE_MAP: Dict[type, str] = {
    int: "int",
    float: "f64",
    bytes: "[]byte",
    str: "string",
    bool: "bool",
    c_int8: "i8",
    c_int16: "i16",
    c_int32: "int",
    c_int64: "i64",
    c_uint8: "byte",
    c_uint16: "u16",
    c_uint32: "u32",
    c_uint64: "u64",
}

V_CONTAINER_TYPE_MAP: Dict[str, str] = {
    "List": "[]",
    "Dict": "map",
    "Set": "set",
    "Optional": "?",
}

V_WIDTH_RANK: Dict[str, int] = {
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


def infer_v_types(node: ast.AST):
    visitor = InferVTypesTransformer()
    visitor.visit(node)


def map_type(typename: str) -> str:
    typeclass = class_for_typename(typename, None)
    return V_TYPE_MAP.get(typeclass, typename)


def get_inferred_v_type(node: ast.AST) -> str:
    if isinstance(node, ast.Call):
        fname = get_id(node.func)
        if fname in {"max", "min", "floor"}:
            return "f64"
    if isinstance(node, ast.Name):
        if not hasattr(node, "scopes"):
            return None
        definition: ast.AST = node.scopes.find(get_id(node))
        # Prevent infinite recursion
        if definition != node:
            return get_inferred_v_type(definition)
    if hasattr(node, "v_annotation"):
        return node.v_annotation
    python_type: ast.AST = get_inferred_type(node)
    return map_type(get_id(python_type))


# Copy pasta from rust. Double check for correctness
class InferVTypesTransformer(ast.NodeTransformer):
    """Implements v type inference logic as opposed to python type inference logic"""

    FIXED_WIDTH_INTS = InferTypesTransformer.FIXED_WIDTH_INTS
    FIXED_WIDTH_INTS_NAME_LIST = InferTypesTransformer.FIXED_WIDTH_INTS_NAME
    FIXED_WIDTH_INTS_NAME = InferTypesTransformer.FIXED_WIDTH_INTS_NAME_LIST

    def __init__(self):
        super().__init__()

    def _handle_overflow(self, op, left_id, right_id):
        left_v_id = map_type(left_id)
        right_v_id = map_type(right_id)

        left_v_rank = V_WIDTH_RANK.get(left_v_id, -1)
        right_v_rank = V_WIDTH_RANK.get(right_v_id, -1)

        return left_id if left_v_rank > right_v_rank else right_id

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
            node.v_annotation = map_type(ret)
            return node
        if left_id == right_id:
            node.annotation = left
            node.v_annotation = map_type(left_id)
            return node
        else:
            if left_id in self.FIXED_WIDTH_INTS_NAME:
                left_id = "int"
            if right_id in self.FIXED_WIDTH_INTS_NAME:
                right_id = "int"
            if (left_id, right_id) in {("int", "float"), ("float", "int")}:
                node.v_annotation = map_type("float")
                return node
            if left_id == "str" and right_id == "int":
                node.v_annotation = map_type("str")
                return node

            raise AstUnrecognisedBinOp(left_id, right_id, node)
