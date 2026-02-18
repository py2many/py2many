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
from py2many.inference import InferTypesTransformer, LanguageInferenceBase, is_reference

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


class RustInference(LanguageInferenceBase):
    TYPE_MAP = RUST_TYPE_MAP
    CONTAINER_TYPE_MAP = RUST_CONTAINER_TYPE_MAP
    WIDTH_RANK = RUST_WIDTH_RANK
    EXTENSION_TYPE_MAP = RUST_EXTENSION_TYPE_MAP

    @classmethod
    def extension_map_type(cls, typename, return_type=False):
        if typename == "_":
            return "&PyAny"
        if typename is None and return_type:
            return "PyResult<()>"

        typeclass = class_for_typename(typename, "&PyAny")

        if typeclass in RUST_EXTENSION_TYPE_MAP:
            if return_type and typeclass is str:
                typename = "String"
                return f"PyResult<{typename}>"
            else:
                return RUST_EXTENSION_TYPE_MAP[typeclass]

        if typeclass in RUST_TYPE_MAP:
            return RUST_TYPE_MAP[typeclass]

        if (
            return_type
            and typename not in InferRustTypesTransformer.FIXED_WIDTH_INTS_NAME
        ):
            return f"PyResult<{typename}>"
        else:
            return typename

    @classmethod
    def map_type(cls, typename, extension=False, return_type=False):
        if extension:
            return cls.extension_map_type(typename, return_type)
        return super().map_type(typename)


def map_type(typename, extension=False, return_type=False):
    return RustInference.map_type(typename, extension, return_type)


def get_inferred_rust_type(node):
    return RustInference.get_inferred_language_type(node, "rust_annotation")


def is_rust_reference(node):
    if not is_reference(node):
        return False
    if isinstance(node, ast.Call):
        definition = node.scopes.find(get_id(node.func))
        needs_reference = getattr(definition, "rust_return_needs_reference", True)
        return needs_reference
    return True


class InferRustTypesTransformer(InferTypesTransformer):
    """Implements rust type inference logic as opposed to python type inference logic"""

    def __init__(self, extension=False):
        super().__init__()
        self._extension = extension

    def _handle_overflow(self, op, left_id, right_id):
        if self._extension:
            left_id = RustInference.extension_map_type(left_id)
            right_id = RustInference.extension_map_type(right_id)
        return RustInference.handle_overflow(op, left_id, right_id)

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
            node.rust_annotation = get_inferred_rust_type(right)
            return node

        if right is None and left is not None:
            node.rust_annotation = get_inferred_rust_type(left)
            return node

        if right is None and left is None:
            return node

        # Both operands are annotated. Now we have interesting cases
        left_id = get_id(left)
        right_id = get_id(right)

        ret = self._handle_overflow(node.op, left_id, right_id)
        node.rust_annotation = ret
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
