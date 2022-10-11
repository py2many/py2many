import ast

from ctypes import c_int8, c_int16, c_int32, c_int64
from ctypes import c_uint8, c_uint16, c_uint32, c_uint64
import re
from typing import Dict, List, Optional, Set, Tuple
from py2many.analysis import IGNORED_MODULE_SET
from py2many.ast_helpers import get_id

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler
from py2many.tracer import find_node_by_name_and_type, find_node_by_type
from pyjl.global_vars import DEFAULT_TYPE, NONE_TYPE

from .plugins import (
    ATTR_DISPATCH_TABLE,
    FUNC_DISPATCH_TABLE,
    DISPATCH_MAP,
    SMALL_DISPATCH_MAP,
    SMALL_USINGS_MAP,
)

# allowed as names in Python but treated as keywords in Julia
julia_keywords = frozenset(
    [
        "abstract",
        "baremodule",
        "begin",
        "break",
        "catch",
        "const",
        "continue",
        "do",
        "else",
        "elseif",
        "end",
        "export",
        "false",
        "finally",
        "for",
        "function",
        "global",
        "if",
        "import",
        "let",
        "local",
        "macro",
        "module",
        "mutable",
        "primitive",
        "quote",
        "return",
        "struct",
        "true",
        "try",
        "type",
        "using",
        "while",
    ]
)

jl_symbols = {
    ast.BitXor: "⊻",
    ast.And: "&&",
    ast.Or: "||",
    ast.Invert: "~",
    ast.Pow: "^",
    ast.MatMult: "*",
    ast.In: "∈",
    ast.NotIn: "∉",
    ast.Eq: "==",
    ast.FloorDiv: "÷",
    ast.Is: "===",
    ast.IsNot: "!==",
}

JULIA_TYPE_MAP = {
    bool: "Bool",
    int: "Int64",
    float: "Float64",
    bytes: "Array{UInt8}",
    str: "String",
    c_int8: "Int8",
    c_int16: "Int16",
    c_int32: "Int32",
    c_int64: "Int64",
    c_uint8: "UInt8",
    c_uint16: "UInt16",
    c_uint32: "UInt32",
    c_uint64: "UInt64",
}

CONTAINER_TYPE_MAP = {
    list: "Vector",
    List: "Vector",
    Dict: "Dict",
    Set: "Set",
    frozenset: "pset",
    Tuple: "Tuple",
    tuple: "Tuple",
    bytearray: f"Vector{{UInt8}}",
}

JL_IGNORED_MODULE_SET = set(
    [
        "unittest",
        "operator",
        "numbers",
        "collections",
        "test",
        "test.support",
        "weakref",
        "pickle",
        "struct",
        "array",
        "itertools",
        "multiprocessing",
        "re",
        "contextlib",
        "time",
        "argparse_dataclass",
        "bisect",
        "base64",
        "binascii",
        "traceback",
        "types",
        "io",
        "random",
        "tempfile",
        "toposort",
        "importlib",
        "importlib.abc",
    ]
)


def jl_symbol(node):
    """Find the equivalent Julia symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return jl_symbols[symbol_type]


class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        self._type_map = JULIA_TYPE_MAP
        self._container_type_map = CONTAINER_TYPE_MAP
        self._default_type = DEFAULT_TYPE
        self._none_type = NONE_TYPE
        self._statement_separator = ""
        self._ignored_module_set = IGNORED_MODULE_SET.copy().union(
            JL_IGNORED_MODULE_SET.copy()
        )
        self._dispatch_map = DISPATCH_MAP
        self._small_dispatch_map = SMALL_DISPATCH_MAP
        self._small_usings_map = SMALL_USINGS_MAP
        self._func_dispatch_table = FUNC_DISPATCH_TABLE
        self._attr_dispatch_table = ATTR_DISPATCH_TABLE
        # PyCall Imports
        self._pycall_imports = set()

    def visit(self, node) -> str:
        if type(node) in jl_symbols:
            return jl_symbol(node)
        else:
            return super().visit(node)

    def visit_Name(self, node) -> str:
        if node.id in julia_keywords:
            return node.id + "_"
        return super().visit_Name(node)

    def visit_BinOp(self, node) -> str:
        if isinstance(node.op, ast.Mult):
            return "{0}*{1}".format(self.visit(node.left), self.visit(node.right))
        if isinstance(node.op, ast.Pow):
            return "{0}^{1}".format(self.visit(node.left), self.visit(node.right))

        bin_op = (
            f"{self.visit(node.left)} {self.visit(node.op)} {self.visit(node.right)}"
        )
        is_nested = getattr(node, "isnested", None)
        return bin_op if not is_nested else f"({bin_op})"

    # =====================================
    # Dispatch Mechanism
    # =====================================

    def _dispatch(
        self,
        node: ast.Call,
        fname: str,
        vargs: List[str],
        kwargs: list[tuple[str, str]],
    ) -> Optional[str]:
        if len(node.args) > 0:
            var = vargs[0]
            if isinstance(node.args[0], ast.Call) and (id := get_id(node.args[0].func)):
                var = id

            dispatch_func = self._get_dispatch_func(node, var, fname, vargs, kwargs)
            if dispatch_func:
                return dispatch_func

            # Remove any extra values
            if re.match(r"\w+", var):
                dispatch = self._clike_dispatch(node, f"{var}.{fname}", vargs, kwargs)
                if dispatch:
                    return dispatch

            # Self argument type lookup
            class_node: ast.ClassDef = find_node_by_type(ast.ClassDef, node.scopes)
            if class_node:
                base_str = self._find_last_base(class_node, "")
                dispatch_func = self._get_dispatch_func(
                    node, base_str, fname, vargs, kwargs
                )
                if dispatch_func:
                    return dispatch_func

            # Dispatch based on annotations
            annotation = None
            if ann := getattr(node.args[0], "annotation", None):
                annotation = ann
            elif not annotation and (v := node.scopes.find(var)):
                annotation = getattr(v, "annotation", None)
            elif ann := getattr(node, "annotation", None):
                annotation = ann

            if ann := self._generic_typename_from_type_node(annotation):
                if isinstance(ann, list):
                    ann = ann[0]
                # Get main type
                ann: str = re.split(r"\[|\]", ann)[0]
                if dispatch_func := self._get_dispatch_func(
                    node, ann, fname, vargs, kwargs
                ):
                    return dispatch_func
                elif dispatch_func := self._clike_dispatch(
                    node, f"{ann}.{fname}", vargs, kwargs
                ):
                    return dispatch_func

        if dispatch_func := self._clike_dispatch(
            node, getattr(node, "orig_name", None), vargs, kwargs
        ):
            # Special attribute used for dispatching
            return dispatch_func
        return self._clike_dispatch(node, fname, vargs, kwargs)

    # Adds kwargs to clike dispatch
    def _clike_dispatch(
        self, node, fname: str, vargs: List[str], kwargs: list[tuple[str, str]]
    ) -> Optional[str]:
        if fname in self._dispatch_map:
            try:
                return self._dispatch_map[fname](self, node, vargs, kwargs)
            except IndexError:
                return None

        if fname in self._small_dispatch_map:
            if fname in self._small_usings_map:
                self._usings.add(self._small_usings_map[fname])
            try:
                return self._small_dispatch_map[fname](node, vargs, kwargs)
            except IndexError:
                return None

        func = self._func_for_lookup(fname)
        if func is not None and func in self._func_dispatch_table:
            if func in self._func_usings_map:
                self._usings.add(self._func_usings_map[func])
            ret, node.result_type = self._func_dispatch_table[func]
            try:
                return ret(self, node, vargs, kwargs)
            except IndexError:
                return None

        # string based fallback
        fname_stem, fname_leaf = self._func_name_split(fname)
        if fname_stem and fname_leaf in self._func_dispatch_table:
            ret, node.result_type = self._func_dispatch_table[fname_leaf]
            try:
                return fname_stem + ret(self, node, vargs, kwargs)
            except IndexError:
                return None
        return None

    def _get_dispatch_func(self, node, class_name, fname, vargs, kwargs):
        py_type = self._func_for_lookup(f"{class_name}.{fname}")
        if py_type in self._func_dispatch_table:
            ret, node.result_type = self._func_dispatch_table[py_type]
            try:
                return ret(self, node, vargs, kwargs)
            except (IndexError, Exception):
                return None

        return None

    def _find_last_base(self, node: ast.ClassDef, base_str):
        for base in node.bases:
            base_str = self.visit(base)
            if superclass := find_node_by_name_and_type(
                base_str, ast.ClassDef, node.scopes
            )[0]:
                # print(superclass.bases)
                return self._find_last_base(superclass, base_str)
        return base_str
