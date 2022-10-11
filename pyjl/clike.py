import ast
import re

from py2many.analysis import IGNORED_MODULE_SET
from py2many.exceptions import AstTypeNotSupported, TypeNotSupported
from py2many.astx import LifeTime
from typing import List, Optional, Tuple, Union
from py2many.ast_helpers import get_id
import logging

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler, class_for_typename
from py2many.external_modules import ExternalBase
from py2many.helpers import get_ann_repr
from py2many.tracer import find_node_by_name_and_type, find_node_by_type
from pyjl.juliaAst import JuliaNodeVisitor
from pyjl.plugins import (
    ATTR_DISPATCH_TABLE,
    FUNC_DISPATCH_TABLE,
    JULIA_SPECIAL_NAME_TABLE,
    MODULE_DISPATCH_TABLE,
    SMALL_DISPATCH_MAP,
    SMALL_USINGS_MAP,
    DISPATCH_MAP,
)
from pyjl.global_vars import (
    ALLOW_ANNOTATIONS_ON_GLOBALS,
    FLAG_DEFAULTS,
    GLOBAL_FLAGS,
    NONE_TYPE,
    SEP,
    USE_MODULES,
)
from pyjl.global_vars import DEFAULT_TYPE

from numbers import Complex, Integral, Rational, Real
from typing import Any, Dict, List, Optional, Set, Tuple

logger = logging.Logger("pyjl")

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
        # "type",
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

JULIA_TYPE_MAP = {
    bool: "Bool",
    int: "Int",
    float: "Float64",
    bytes: "Array{UInt8}",
    str: "String",
    Integral: "Integer",
    complex: "Complex",
    Complex: "Complex",
    Rational: "Rational",
    Real: "Real",
    None: "Nothing",
    Any: "Any",
    object: "DataType",
}

# Used for types that cannot be
# represented in a dictionary
JULIA_STR_TYPE_MAP = {"function": "Function"}

JULIA_INTEGER_TYPES = [
    "Int",
    "Int8",
    "Int16",
    "Int32",
    "Int64",
    "UInt128",
    "UInt64",
    "UInt32",
    "UInt16",
    "UInt8",
    "Integer",
]

JULIA_NUM_TYPES = JULIA_INTEGER_TYPES + ["Float16", "Float32", "Float64"]

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

RESERVED_TYPEVARS = {
    "BLiteral",
    "OLiteral",
    "HLiteral",
    "BigInt",
    "BigFloat"
}


def jl_symbol(node):
    """Find the equivalent Julia symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return jl_symbols[symbol_type]


class CLikeTranspiler(CommonCLikeTranspiler, JuliaNodeVisitor, ExternalBase):
    def __init__(self):
        super().__init__()
        self._type_map = JULIA_TYPE_MAP
        self._str_type_map = JULIA_STR_TYPE_MAP
        self._container_type_map = CONTAINER_TYPE_MAP
        self._default_type = DEFAULT_TYPE
        self._none_type = NONE_TYPE
        self._statement_separator = ""
        self._ignored_module_set = IGNORED_MODULE_SET.copy().union(
            JL_IGNORED_MODULE_SET.copy()
        )
        self._julia_keywords = julia_keywords
        self._dispatch_map = DISPATCH_MAP
        self._small_dispatch_map = SMALL_DISPATCH_MAP
        self._small_usings_map = SMALL_USINGS_MAP
        self._func_dispatch_table = FUNC_DISPATCH_TABLE
        self._attr_dispatch_table = ATTR_DISPATCH_TABLE
        #
        self._reserved_typevars = RESERVED_TYPEVARS
        self._generics = [] # List containing generic types
        self._use_modules = None
        self._external_type_map = {}
        self._flags = None
        self._module_dispatch_table = MODULE_DISPATCH_TABLE
        self._special_names_dispatch_table = JULIA_SPECIAL_NAME_TABLE
        self._allow_annotations_on_globals = False
        self._pycall_imports = set()
        # Get external module features
        self.import_external_modules(self.NAME)

    def usings(self):
        usings = sorted(list(set(self._usings)))
        uses = "\n".join(f"using {mod}" for mod in usings)
        return uses

    def headers(self, meta=None):
        if self._flags:
            flags_in_use = "\n".join(self._flags)
            return f"# Transpiled with flags: \n{flags_in_use}"

    def visit(self, node) -> str:
        if type(node) in jl_symbols:
            return jl_symbol(node)
        else:
            return super().visit(node)

    def visit_Module(self, node: ast.Module) -> str:
        self._use_modules = getattr(node, USE_MODULES, FLAG_DEFAULTS[USE_MODULES])
        self._flags = [
            f"# - {flag}" for flag in GLOBAL_FLAGS if getattr(node, flag, False)
        ]
        self._allow_annotations_on_globals = getattr(
            node,
            ALLOW_ANNOTATIONS_ON_GLOBALS,
            FLAG_DEFAULTS[ALLOW_ANNOTATIONS_ON_GLOBALS],
        )
        return super().visit_Module(node)

    def visit_arg(self, node):
        # if node.arg == "self":
        #     return (None, "self")
        # typename = "T"
        typename = ""
        if getattr(node, "annotation", None):
            typename = self.visit(node.annotation)
        elif hasattr(node, "annotation") and (
            t_name := self._typename_from_annotation(node)
        ):
            typename = t_name
        return (typename, node.arg)

    def visit_arguments(self, node: ast.arguments) -> Tuple[List[str], List[str]]:
        args = [self.visit(arg) for arg in node.args]
        if args == []:
            return [], []
        typenames, args = map(list, zip(*args))
        # Replace julia keywords
        args = [a if a not in self._julia_keywords else f"{a}_" for a in args]
        return typenames, args

    def visit_BinOp(self, node) -> str:
        node_op = self.visit(node.op)
        op = f".{node_op}" if getattr(node, "broadcast", False) else node_op

        if isinstance(node.op, ast.Mult):
            return f"{self.visit(node.left)}{op}{self.visit(node.right)}"
        if isinstance(node.op, ast.Pow):
            return f"{self.visit(node.left)}{op}{self.visit(node.right)}"

        bin_op = f"{self.visit(node.left)} {op} {self.visit(node.right)}"
        is_nested = getattr(node, "isnested", None)
        return bin_op if not is_nested else f"({bin_op})"

    def visit_NamedExpr(self, node: ast.NamedExpr) -> str:
        return f"({self.visit(node.target)} = {self.visit(node.value)})"

    def visit_keyword(self, node: ast.keyword) -> Any:
        arg_str = node.arg if node.arg not in self._julia_keywords else f"{node.arg}_"
        return f"{arg_str} = {self.visit(node.value)}"

    def visit_ImportFrom(self, node) -> str:
        if node.module in self._ignored_module_set:
            return ""

        imported_name = node.module
        if not node.module:
            # Import from '.'
            imported_name = "."

        # PyJL requires aliases
        names = [self.visit(n) for n in node.names]
        return self._import_from(imported_name, names, node.level)

    ######################################################
    ################### Type Mappings ####################
    ######################################################

    def _map_type(self, typename: str, lifetime=LifeTime.UNKNOWN) -> str:
        typeclass = self._func_for_lookup(typename)
        if typeclass is None and typename != "None":
            return typename
        if typename in self._str_type_map:
            return self._str_type_map[typename]
        elif typeclass in self._type_map:
            return self._type_map[typeclass]
        elif typeclass in self._container_type_map:
            return self._container_type_map[typeclass]
        elif typename in self._module_dispatch_table:
            return self._module_dispatch_table[typeclass]
        elif typeclass in self._external_type_map:
            return self._external_type_map[typeclass](self)
        else:
            # Default if no type is found
            return typename

    def _map_container_type(self, typename) -> str:
        typeclass = self._func_for_lookup(typename)
        return self._container_type_map.get(typeclass, self._default_type)

    def _typename_from_annotation(self, node, attr="annotation") -> str:
        typename = self._default_type
        if type_node := getattr(node, attr, None):
            typename = self._typename_from_type_node(
                type_node, parse_func=self._map_type, default=self._default_type
            )
            if isinstance(type_node, ast.Subscript):
                node.container_type = tuple(
                    map(self._map_type, type_node.container_type)
                )
            if isinstance(type_node, ast.Name):
                id = self._map_type(get_id(node))
                if self._func_for_lookup(id) in self._container_type_map:
                    node.container_type = (id, "Any")

            if cont_type := getattr(node, "container_type", None):
                try:
                    return self._visit_container_type(cont_type)
                except TypeNotSupported as e:
                    raise AstTypeNotSupported(str(e), node)
            if self.not_inferable(node, type_node) and typename is None:
                # raise AstCouldNotInfer(type_node, node)
                return None
        return typename

    def not_inferable(self, node, type_node):
        return (
            node is None
            or (isinstance(node, ast.arg))
            # (isinstance(node, ast.arg) and node.arg == "self")
            or isinstance(type_node, ast.Constant)
        )

    def _typename_from_type_node(
        self, node, parse_func=None, default=None
    ) -> Union[List, str, None]:
        if isinstance(node, ast.Name):
            return self._map_type(
                get_id(node), getattr(node, "lifetime", LifeTime.UNKNOWN)
            )
        elif isinstance(node, ast.Attribute):
            node_id = get_id(node)
            if node_id and node_id.startswith("typing."):
                node_id = node_id.split(".")[1]
            if (mapped_id := self._map_type(node_id)) != node_id:
                return mapped_id
            return f"{self._typename_from_type_node(node.value, parse_func, default)}.{self._map_type(node.attr)}"
        elif isinstance(node, ast.Subscript):
            (value_type, index_type) = tuple(
                map(
                    lambda x: self._typename_from_type_node(x, parse_func, default),
                    (node.value, node.slice),
                )
            )
            node.container_type = (value_type, index_type)
            return f"{value_type}{{{index_type}}}"
        elif isinstance(node, ast.Constant):
            if node.value in JULIA_TYPE_MAP:
                # Can't use self._map_type, as it uses self._func_for_lookup.
                # By supplying the type None, it will not work
                return JULIA_TYPE_MAP[node.value]
        elif isinstance(node, ast.Tuple) or isinstance(node, ast.List):
            elts = list(
                map(
                    lambda x: self._typename_from_type_node(x, parse_func, default),
                    node.elts,
                )
            )
            return ", ".join(elts)
        return default

    def _combine_value_index(self, value_type, index_type) -> str:
        return f"{value_type}{{{index_type}}}"

    def _visit_container_type(self, typename: Tuple) -> str:
        value_type, index_type = typename
        if isinstance(index_type, List):
            parsed_items = []
            for it in index_type:
                parsed_items.append(self._map_type(it))
            index_type = ", ".join(parsed_items)
        else:
            index_type = self._map_type(index_type)
        value_type = self._map_type(value_type)
        return self._combine_value_index(value_type, index_type)

    ################################################
    ######### For Type Inference Mechanism #########
    ################################################

    def _func_for_lookup(self, fname) -> Union[str, object]:
        func = class_for_typename(fname, self._default_type, self._imported_names)
        if func is None:
            return None
        try:
            hash(func)
        except TypeError:
            logger.debug(f"{func} is not hashable")
            return None
        return func

    def _dispatch(
        self, node: ast.Call, fname: str, vargs: List[str], kwargs: list[tuple[str,str]]
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

        if dispatch_func := self._clike_dispatch(node, 
                getattr(node, "orig_name", None), vargs, kwargs):
            # Special attribute used for dispatching
            return dispatch_func
        return self._clike_dispatch(node, fname, vargs, kwargs)

    # Adds kwargs to clike dispatch
    def _clike_dispatch(
        self, node, fname: str, vargs: List[str], kwargs: list[tuple[str,str]]
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
            base_str = get_ann_repr(base, sep=SEP)
            if superclass := find_node_by_name_and_type(
                base_str, ast.ClassDef, node.scopes
            )[0]:
                return self._find_last_base(superclass, base_str)
        return base_str
