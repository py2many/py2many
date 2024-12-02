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

GO_TYPE_MAP = {
    bool: "bool",
    int: "int",
    float: "float64",
    bytes: "[]uint8",
    str: "string",
    c_int8: "int8",
    c_int16: "int16",
    c_int32: "int32",
    c_int64: "int64",
    c_uint8: "uint8",
    c_uint16: "uint16",
    c_uint32: "uint32",
    c_uint64: "uint64",
}

GO_CONTAINER_TYPE_MAP = {"List": "[]", "Dict": None, "Set": None, "Optional": "nil"}


GO_WIDTH_RANK = {
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
}


def infer_go_types(node):
    visitor = InferGoTypesTransformer()
    visitor.visit(node)


def map_type(typename):
    typeclass = class_for_typename(typename, None)
    if typeclass in GO_TYPE_MAP:
        return GO_TYPE_MAP[typeclass]
    return typename


def get_inferred_go_type(node):
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
            return get_inferred_go_type(definition)
    if hasattr(node, "go_annotation"):
        return node.go_annotation
    python_type = get_inferred_type(node)
    return map_type(get_id(python_type))


# Copy pasta from rust. Double check for correctness
class InferGoTypesTransformer(ast.NodeTransformer):
    """Implements go type inference logic as opposed to python type inference logic"""

    FIXED_WIDTH_INTS = InferTypesTransformer.FIXED_WIDTH_INTS
    FIXED_WIDTH_INTS_NAME_LIST = InferTypesTransformer.FIXED_WIDTH_INTS_NAME
    FIXED_WIDTH_INTS_NAME = InferTypesTransformer.FIXED_WIDTH_INTS_NAME_LIST

    def _handle_overflow(self, op, left_id, right_id):
        left_go_id = map_type(left_id)
        right_go_id = map_type(right_id)

        left_go_rank = GO_WIDTH_RANK.get(left_go_id, -1)
        right_go_rank = GO_WIDTH_RANK.get(right_go_id, -1)

        return left_go_id if left_go_rank > right_go_rank else right_go_id

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
            node.go_annotation = get_inferred_go_type(right)
            return node

        if right is None and left is not None:
            node.go_annotation = get_inferred_go_type(left)
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
            node.go_annotation = ret
            return node
        if left_id == right_id:
            node.annotation = left
            node.go_annotation = map_type(left_id)
            return node
        else:
            if left_id in self.FIXED_WIDTH_INTS_NAME:
                left_id = "int"
            if right_id in self.FIXED_WIDTH_INTS_NAME:
                right_id = "int"
            if (left_id, right_id) in {("int", "float"), ("float", "int")}:
                node.go_annotation = map_type("float")
                return node

            raise AstUnrecognisedBinOp(left_id, right_id, node)
