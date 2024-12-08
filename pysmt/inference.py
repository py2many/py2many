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
from py2many.clike import class_for_typename
from py2many.exceptions import AstUnrecognisedBinOp
from py2many.inference import InferTypesTransformer, get_inferred_type

SMT_TYPE_MAP = {
    int: "Int",
    float: "Float64",
    bytes: "openArray[byte]",
    str: "string",
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


def infer_smt_types(node: ast.AST):
    visitor = InferSmtTypesTransformer()
    visitor.visit(node)


def map_type(typename):
    typeclass = class_for_typename(typename, None)
    if typeclass in SMT_TYPE_MAP:
        return SMT_TYPE_MAP[typeclass]
    return typename


def get_inferred_smt_type(node):
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
            return get_inferred_smt_type(definition)
    if hasattr(node, "smt_annotation"):
        return node.smt_annotation
    python_type = get_inferred_type(node)
    return map_type(get_id(python_type))


# Copy pasta from rust. Double check for correctness
class InferSmtTypesTransformer(ast.NodeTransformer):
    """Implements smt type inference logic as opposed to python type inference logic"""

    FIXED_WIDTH_INTS = InferTypesTransformer.FIXED_WIDTH_INTS
    FIXED_WIDTH_INTS_NAME_LIST = InferTypesTransformer.FIXED_WIDTH_INTS_NAME
    FIXED_WIDTH_INTS_NAME = InferTypesTransformer.FIXED_WIDTH_INTS_NAME_LIST

    def _handle_overflow(self, op, left_id, right_id):
        left_smt_id = map_type(left_id)
        right_smt_id = map_type(right_id)

        left_smt_rank = SMT_WIDTH_RANK.get(left_smt_id, -1)
        right_smt_rank = SMT_WIDTH_RANK.get(right_smt_id, -1)

        return left_smt_id if left_smt_rank > right_smt_rank else right_smt_id

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
            node.smt_annotation = ret
            return node
        if left_id == right_id:
            node.annotation = left
            node.smt_annotation = map_type(left_id)
            return node
        else:
            if left_id in self.FIXED_WIDTH_INTS_NAME:
                left_id = "int"
            if right_id in self.FIXED_WIDTH_INTS_NAME:
                right_id = "int"
            if (left_id, right_id) in {("int", "float"), ("float", "int")}:
                node.smt_annotation = map_type("float")
                return node

            raise AstUnrecognisedBinOp(left_id, right_id, node)
