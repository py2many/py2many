import ast
import re

from py2many.analysis import IGNORED_MODULE_SET
from py2many.exceptions import AstTypeNotSupported, TypeNotSupported
from py2many.astx import LifeTime
from typing import  List, Optional, Tuple, Union
from py2many.ast_helpers import get_id
import logging

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler, class_for_typename
from py2many.external_modules import ExternalBase
from py2many.helpers import get_ann_repr
from py2many.tracer import find_node_by_type
from pyjl.juliaAst import JuliaNodeVisitor
from pyjl.plugins import ATTR_DISPATCH_TABLE, FUNC_DISPATCH_TABLE, JULIA_SPECIAL_NAME_TABLE, MODULE_DISPATCH_TABLE, SMALL_DISPATCH_MAP, SMALL_USINGS_MAP
from pyjl.global_vars import NONE_TYPE, SEP, USE_MODULES
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
        "type",
        "using",
        "while",
    ]
)

jl_symbols = {
    ast.BitXor: " ⊻ ", 
    ast.And: " && ", 
    ast.Or: " || ",
    ast.Invert: "~",
    ast.Pow: "^",
    ast.MatMult: "*",
    ast.In: "∈",
    ast.NotIn: "∉",
    ast.Eq: "==",
    ast.FloorDiv: "÷",
    ast.Is: "===",
    ast.IsNot: "!=="
}

JL_IGNORED_MODULE_SET = set([
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
    "random"
])

JULIA_TYPE_MAP = {
    bool: "Bool",
    int: "Int64",
    float: "Float64",
    bytes: "Array{UInt8}",
    str: "String",
    Integral: "Integer",
    complex: "Complex",
    Complex: "Complex",
    Rational: "Rational",
    Real: "Real",
    None: "Nothing",
    Any: "Any"
}

JULIA_INTEGER_TYPES = \
    [
        "Int8",
        "Int16",
        "Int32",
        "Int64",
        "UInt128",
        "UInt64",
        "UInt32",
        "UInt16",
        "UInt8",
        "Integer"
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
    bytearray: f"Vector{{Int8}}",
}

def jl_symbol(node):
    """Find the equivalent Julia symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return jl_symbols[symbol_type]

class CLikeTranspiler(CommonCLikeTranspiler, JuliaNodeVisitor, ExternalBase):
    def __init__(self):
        super().__init__()
        self._type_map = JULIA_TYPE_MAP
        self._container_type_map = CONTAINER_TYPE_MAP
        self._default_type = DEFAULT_TYPE
        self._none_type = NONE_TYPE
        self._statement_separator = ""
        self._ignored_module_set = IGNORED_MODULE_SET.copy().union(JL_IGNORED_MODULE_SET.copy())
        self._julia_keywords = julia_keywords
        self._small_dispatch_map = SMALL_DISPATCH_MAP
        self._small_usings_map = SMALL_USINGS_MAP
        self._func_dispatch_table = FUNC_DISPATCH_TABLE
        self._attr_dispatch_table = ATTR_DISPATCH_TABLE
        #
        self._use_modules = None
        self._external_type_map = {}
        self._module_dispatch_table = MODULE_DISPATCH_TABLE
        self._special_names_dispatch_table = JULIA_SPECIAL_NAME_TABLE 
        # Get external module features
        self.import_external_modules(self.NAME)

    def usings(self):
        usings = sorted(list(set(self._usings)))
        uses = "\n".join(f"using {mod}" for mod in usings)
        return uses
        
    def visit(self, node) -> str:
        if type(node) in jl_symbols:
            return jl_symbol(node)
        else:
            return super().visit(node)

    def visit_Module(self, node: ast.Module) -> str:
        self._use_modules = getattr(node, USE_MODULES, None)
        return super().visit_Module(node)

    def visit_Name(self, node) -> str:
        node_id = get_id(node)
        if node_id in self._julia_keywords and \
                not getattr(node, "preserve_keyword", False):
            return f"{node_id}_"
        elif node_id in self._special_names_dispatch_table:
            return self._special_names_dispatch_table[node_id]
        elif getattr(node, "is_annotation", False) or \
                (not getattr(node, "lhs", False) and
                    hasattr(node, "scopes") and
                    not node.scopes.find(node_id) and 
                    not getattr(node, "in_call", None)):
            return self._map_type(node_id)
        return super().visit_Name(node)

    def visit_arg(self, node):
        # if node.arg == "self":
        #     return (None, "self")
        # typename = "T"
        typename = ""
        if getattr(node, "annotation", None):
            typename = self.visit(node.annotation)
        elif hasattr(node, "annotation") and \
                (t_name := self._typename_from_annotation(node)):
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
        op = f".{node_op}" if getattr(node, "broadcast", False) \
            else node_op

        if isinstance(node.op, ast.Mult):
            return f"{self.visit(node.left)}{op}{self.visit(node.right)}"
        if isinstance(node.op, ast.Pow):
            return f"{self.visit(node.left)}{op}{self.visit(node.right)}"

        bin_op = f"{self.visit(node.left)} {op} {self.visit(node.right)}"
        is_nested = getattr(node, "isnested", None)
        return bin_op if not is_nested else f"({bin_op})"

    def visit_In(self, node) -> str:
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        return f"{left} in {right}"

    def visit_NamedExpr(self, node: ast.NamedExpr) -> str:
        return f"({self.visit(node.target)} = {self.visit(node.value)})"

    def visit_keyword(self, node: ast.keyword) -> Any:
        arg_str = node.arg if node.arg not in self._julia_keywords else f"{node.arg}_"
        return f"{arg_str} = {self.visit(node.value)}"

    ######################################################
    ################### Type Mappings ####################
    ######################################################

    def _map_type(self, typename: str, lifetime=LifeTime.UNKNOWN) -> str:
        typeclass = self._func_for_lookup(typename)
        if typeclass is None and typename != "None":
            return typename
        elif typeclass in self._type_map:
            return self._type_map[typeclass]
        elif typeclass in self._container_type_map:
            return self._container_type_map[typeclass]
        elif typeclass in self._module_dispatch_table:
            return self._module_dispatch_table[typeclass]
        elif typeclass in self._external_type_map:
            return self._external_type_map[typeclass]
        else:
            # Default if no type is found
            return typename

    def _map_container_type(self, typename) -> str:
        typeclass = self._func_for_lookup(typename)
        return self._container_type_map.get(typeclass, self._default_type)

    def _typename_from_annotation(self, node, attr="annotation") -> str:
        typename = self._default_type
        if type_node := getattr(node, attr, None):
            typename = self._typename_from_type_node(type_node, 
                parse_func=self._map_type, default=self._default_type)
            if isinstance(type_node, ast.Subscript):
                node.container_type = tuple(map(self._map_type, type_node.container_type))
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
            node is None or
            (isinstance(node, ast.arg))
            # (isinstance(node, ast.arg) and node.arg == "self") 
            or isinstance(type_node, ast.Constant)
        )
    
    def _typename_from_type_node(self, node, parse_func = None, default = None) -> Union[List, str, None]:
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
                map(lambda x: self._typename_from_type_node(x, parse_func, default), 
                    (node.value, node.slice))
            )
            node.container_type = (value_type, index_type)
            return f"{value_type}{{{index_type}}}"
        elif isinstance(node, ast.Constant):
            return self._map_type(node.value)
        elif isinstance(node, ast.Tuple) \
                or isinstance(node, ast.List):
            elts = list(map(
                lambda x: self._typename_from_type_node(x, parse_func, default), node.elts))
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

    def _dispatch(self, node: ast.Call, fname: str, vargs: List[str]) -> Optional[str]:
        if len(node.args) > 0:
            var = vargs[0]
            if isinstance(node.args[0], ast.Call) and \
                    (id := get_id(node.args[0].func)):
                var = id

            # Self argument type lookup
            class_node: ast.ClassDef = find_node_by_type(ast.ClassDef, node.scopes)
            if class_node:
                for base in class_node.bases:
                    base_str = get_ann_repr(base, sep = SEP)
                    dispatch_func = self._get_dispatch_func(node, base_str, fname, vargs)
                    if dispatch_func:
                        return dispatch_func

            # Account for JuliaMethodCallRewriter
            annotation = None
            if ann := getattr(node.args[0], "annotation", None):
                annotation = ann
            if not annotation and (v := node.scopes.find(var)):
                annotation = getattr(v, "annotation", None)

            if ann := self._generic_typename_from_type_node(annotation):
                if isinstance(ann, list):
                    ann = ann[0]
                # Get main type
                ann: str = re.split(r"\[|\]", ann)[0]
                dispatch_func = self._get_dispatch_func(node, ann, fname, vargs)
                if dispatch_func:
                    return dispatch_func

            dispatch_func = self._get_dispatch_func(node, var, fname, vargs[1:])
            if dispatch_func:
                return dispatch_func

            # Remove any extra values
            if re.match(r"\w+", var):
                dispatch = super()._dispatch(node, f"{var}.{fname}", vargs[1:])
                if dispatch:
                    return dispatch
        if hasattr(node, "orig_name"):
            return super()._dispatch(node, node.orig_name, vargs)

        return super()._dispatch(node, fname, vargs)

    def _get_dispatch_func(self, node, class_name, fname, vargs):
        py_type = self._func_for_lookup(f"{class_name}.{fname}")
        if py_type in self._func_dispatch_table:
            ret, node.result_type = self._func_dispatch_table[py_type]
            try:
                return ret(self, node, vargs)
            except (IndexError, Exception):
                return None

        return None
        