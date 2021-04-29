import ast
from py2many.inference import get_inferred_type

from ctypes import c_int8, c_int16, c_int32, c_int64
from ctypes import c_uint8, c_uint16, c_uint32, c_uint64

from py2many.analysis import get_id

GO_TYPE_MAP = {
    "bool": "bool",
    "int": "int",
    "float": "float64",
    "bytes": "[]uint8",
    "str": "string",
    "c_int8": "int8",
    "c_int16": "int16",
    "c_int32": "int32",
    "c_int64": "int64",
    "c_uint8": "uint8",
    "c_uint16": "uint16",
    "c_uint32": "uint32",
    "c_uint64": "uint64",
}


GO_WIDTH_RANK = {
    "int8": 0,
    "uint8": 1,
    "int16": 2,
    "uint16": 3,
    "int32": 4,
    "uint32": 5,
    "int64": 6,
    "uint64": 7,
    "float32": 8,
    "float64": 9,
}


def infer_go_types(node):
    visitor = InferGoTypesTransformer()
    visitor.visit(node)


def map_type(typename):
    if typename in GO_TYPE_MAP:
        return GO_TYPE_MAP[typename]
    return typename


def get_inferred_go_type(node):
    if isinstance(node, ast.Call):
        fname = get_id(node.func)
        if fname.startswith("math"):
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
        left_go_id = map_type(left_id)
        right_go_id = map_type(right_id)

        left_go_rank = GO_WIDTH_RANK.get(left_go_id, -1)
        right_go_rank = GO_WIDTH_RANK.get(right_go_id, -1)

        return left_id if left_go_rank > right_go_rank else right_id

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
            node.go_annotation = map_type(get_id(right))
            return node

        if right is None and left is not None:
            node.go_annotation = map_type(get_id(left))
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
            node.go_annotation = map_type(ret)
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

            raise Exception(f"type error: {left_id} {type(node.op)} {right_id}")
