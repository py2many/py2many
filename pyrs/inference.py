import ast

from py2many.inference import get_inferred_type, is_reference, InferTypesTransformer
from py2many.analysis import get_id, is_mutable

RUST_TYPE_MAP = {
    "int": "i32",
    "float": "f64",
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
    "bool": 0,
    "i8": 1,
    "u8": 2,
    "i16": 3,
    "u16": 4,
    "i32": 5,
    "u32": 6,
    "i64": 7,
    "u64": 8,
    "f32": 9,
    "f64": 10,
}


def infer_rust_types(node):
    visitor = InferRustTypesTransformer()
    visitor.visit(node)


def map_type(typename):
    if typename in RUST_TYPE_MAP:
        return RUST_TYPE_MAP[typename]
    return typename


def is_rust_reference(node):
    if not is_reference(node):
        return False
    if isinstance(node, ast.Call):
        definition = node.scopes.find(get_id(node.func))
        needs_reference = getattr(definition, "rust_return_needs_reference", True)
        return needs_reference
    return True


def get_inferred_rust_type(node):
    if hasattr(node, "rust_annotation"):
        return node.rust_annotation
    if isinstance(node, ast.Name):
        if not hasattr(node, "scopes"):
            return None
        definition = node.scopes.find(get_id(node))
        # Prevent infinite recursion
        if definition != node:
            return get_inferred_rust_type(definition)
    python_type = get_inferred_type(node)
    ret = map_type(get_id(python_type))
    node.rust_annotation = ret
    return ret


class InferRustTypesTransformer(ast.NodeTransformer):
    """Implements rust type inference logic as opposed to python type inference logic"""

    FIXED_WIDTH_INTS = InferTypesTransformer.FIXED_WIDTH_INTS
    FIXED_WIDTH_INTS_NAME_LIST = InferTypesTransformer.FIXED_WIDTH_INTS_NAME
    FIXED_WIDTH_INTS_NAME = InferTypesTransformer.FIXED_WIDTH_INTS_NAME_LIST

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

    def visit_Return(self, node):
        self.generic_visit(node)
        if node.value:
            fndef = None
            for scope in node.scopes:
                if isinstance(scope, ast.FunctionDef):
                    fndef = scope
                    break
            if fndef:
                if is_reference(node.value):
                    mut = is_mutable(node.scopes, get_id(node.value))
                    fndef.returns.rust_needs_reference = not mut
                    fndef.rust_return_needs_reference = (
                        fndef.returns.rust_needs_reference
                    )
        return node
