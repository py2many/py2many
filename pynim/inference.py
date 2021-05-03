import ast

from py2many.inference import get_inferred_type, InferTypesTransformer
from py2many.analysis import get_id


NIM_TYPE_MAP = {
    "int": "int",
    "float": "float64",
    "bytes": "openArray[byte]",
    "str": "string",
    "bool": "bool",
    "c_int8": "int8",
    "c_int16": "int16",
    "c_int32": "int32",
    "c_int64": "int64",
    "c_uint8": "uint8",
    "c_uint16": "uint16",
    "c_uint32": "uint32",
    "c_uint64": "uint64",
}

NIM_WIDTH_RANK = {
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


def infer_nim_types(node):
    visitor = InferNimTypesTransformer()
    visitor.visit(node)


def map_type(typename):
    if typename in NIM_TYPE_MAP:
        return NIM_TYPE_MAP[typename]
    return typename


def get_inferred_nim_type(node):
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
            return get_inferred_nim_type(definition)
    if hasattr(node, "nim_annotation"):
        return node.nim_annotation
    python_type = get_inferred_type(node)
    return map_type(get_id(python_type))


# Copy pasta from rust. Double check for correctness
class InferNimTypesTransformer(ast.NodeTransformer):
    """Implements nim type inference logic as opposed to python type inference logic"""

    FIXED_WIDTH_INTS = InferTypesTransformer.FIXED_WIDTH_INTS
    FIXED_WIDTH_INTS_NAME_LIST = InferTypesTransformer.FIXED_WIDTH_INTS_NAME
    FIXED_WIDTH_INTS_NAME = InferTypesTransformer.FIXED_WIDTH_INTS_NAME_LIST

    def __init__(self):
        super().__init__()

    def _handle_overflow(self, op, left_id, right_id):
        left_nim_id = map_type(left_id)
        right_nim_id = map_type(right_id)

        left_nim_rank = NIM_WIDTH_RANK.get(left_nim_id, -1)
        right_nim_rank = NIM_WIDTH_RANK.get(right_nim_id, -1)

        return left_id if left_nim_rank > right_nim_rank else right_id

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
            node.nim_annotation = get_inferred_nim_type(right)
            return node

        if right is None and left is not None:
            node.nim_annotation = get_inferred_nim_type(left)
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
            node.nim_annotation = map_type(ret)
            return node
        if left_id == right_id:
            node.annotation = left
            node.nim_annotation = map_type(left_id)
            return node
        else:
            if left_id in self.FIXED_WIDTH_INTS_NAME:
                left_id = "int"
            if right_id in self.FIXED_WIDTH_INTS_NAME:
                right_id = "int"
            if (left_id, right_id) in {("int", "float"), ("float", "int")}:
                node.nim_annotation = map_type("float")
                return node

            raise Exception(f"type error: {left_id} {type(node.op)} {right_id}")
