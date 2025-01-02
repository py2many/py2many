import ast
import datetime
import io
import types
import typing
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

from py2many.analysis import get_id, is_mutable
from py2many.clike import class_for_typename
from py2many.exceptions import AstUnrecognisedBinOp
from py2many.inference import InferTypesTransformer, get_inferred_type, is_reference

RUST_TYPE_MAP = {
    int: "i32",
    float: "f64",
    bytes: "&[u8]",
    str: "&str",
    bool: "bool",
    c_int8: "i8",
    c_int16: "i16",
    c_int32: "i32",
    c_int64: "i64",
    c_uint8: "u8",
    c_uint16: "u16",
    c_uint32: "u32",
    c_uint64: "u64",
    io.RawIOBase: "std::fs::File",
}

RUST_CONTAINER_TYPE_MAP = {
    "List": "Vec",
    "Dict": "HashMap",
    "Set": "HashSet",
    "Optional": "Option",
    "Result": "Result",
}

# https://pyo3.rs/v0.13.2/conversions/tables.html
RUST_EXTENSION_TYPE_MAP = {
    str: "&PyUnicode",
    bytes: "&PyBytes",
    complex: "&PyComplex",
    list: "&PyList",
    dict: "&PyDict",
    tuple: "&PyTuple",
    set: "&PySet",
    frozenset: "&PyFrozenSet",
    bytearray: "&PyByteArray",
    slice: "&PySlice",
    type: "&PyType",
    types.ModuleType: "&PyModule",
    datetime.datetime: "&PyDateTime",
    datetime.date: "&PyDate",
    datetime.time: "&PyTime",
    datetime.tzinfo: "&PyTzInfo",
    datetime.timedelta: "&PyDelta",
    typing.Sequence: "&PySequence",
    typing.Iterator: "&PyIterator",
    object: "&PyAny",
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

RUST_RANK_TO_TYPE = {v: k for k, v in RUST_WIDTH_RANK.items()}


class InferRustTypesTransformer(ast.NodeTransformer):
    """Implements rust type inference logic as opposed to python type inference logic"""

    FIXED_WIDTH_INTS = InferTypesTransformer.FIXED_WIDTH_INTS
    FIXED_WIDTH_INTS_NAME_LIST = InferTypesTransformer.FIXED_WIDTH_INTS_NAME
    FIXED_WIDTH_INTS_NAME = InferTypesTransformer.FIXED_WIDTH_INTS_NAME_LIST

    def __init__(self, extension):
        super().__init__()
        self._extension = extension

    def _handle_overflow(self, op, left_id, right_id):
        left_rust_id = map_type(left_id)
        right_rust_id = map_type(right_id)

        left_rust_rank = RUST_WIDTH_RANK.get(left_rust_id, -1)
        right_rust_rank = RUST_WIDTH_RANK.get(right_rust_id, -1)

        return left_rust_id if left_rust_rank > right_rust_rank else right_rust_id

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
            node.rust_annotation = map_type(left_id)
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
            node.rust_annotation = ret
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

            LEGAL_COMBINATIONS = {
                ("str", ast.Mult),
                ("str", ast.Mod),
                ("List", ast.Add),
            }

            if (
                left_id is not None
                and (left_id, type(node.op)) not in LEGAL_COMBINATIONS
            ):
                raise AstUnrecognisedBinOp(left_id, right_id, node)

        return node

    def visit_FunctionDef(self, node):
        node.no_return = True
        node.rust_pyresult_type = self._extension
        self.generic_visit(node)
        return node

    def visit_Return(self, node):
        self.generic_visit(node)
        fndef = None
        for scope in node.scopes:
            if isinstance(scope, ast.FunctionDef):
                fndef = scope
                break
        if fndef:
            fndef.no_return = False
        if node.value:
            if fndef and fndef.returns:
                if is_reference(node.value):
                    mut = is_mutable(node.scopes, get_id(node.value))
                    fndef.returns.rust_needs_reference = not mut
                    fndef.rust_return_needs_reference = (
                        fndef.returns.rust_needs_reference
                    )
        return node


def infer_rust_types(node, extension=False):
    visitor = InferRustTypesTransformer(extension)
    visitor.visit(node)


def extension_map_type(typename, return_type=False):
    if typename == "_":
        return "&PyAny"
    if typename == None and return_type:
        return "PyResult<()>"

    typeclass = class_for_typename(typename, "&PyAny")

    if typeclass in RUST_EXTENSION_TYPE_MAP:
        if return_type and typeclass == str:
            typename = "String"
            return f"PyResult<{typename}>"
        else:
            return RUST_EXTENSION_TYPE_MAP[typeclass]

    if typeclass in RUST_TYPE_MAP:
        return RUST_TYPE_MAP[typeclass]

    if return_type and typename not in InferRustTypesTransformer.FIXED_WIDTH_INTS_NAME:
        return f"PyResult<{typename}>"
    else:
        return typename


def map_type(typename, extension=False, return_type=False):
    if extension:
        return extension_map_type(typename, return_type)
    typeclass = class_for_typename(typename, "&PyAny")
    if typeclass in RUST_TYPE_MAP:
        return RUST_TYPE_MAP[typeclass]
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
        if definition and definition != node:
            return get_inferred_rust_type(definition)
    python_type = get_inferred_type(node)
    ret = map_type(get_id(python_type))
    node.rust_annotation = ret
    return ret
