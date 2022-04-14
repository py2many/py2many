import ast
from operator import index
import re
from py2many.analysis import IGNORED_MODULE_SET
from py2many.exceptions import AstTypeNotSupported, TypeNotSupported
from py2many.astx import LifeTime
from typing import List, Optional, Tuple, Union
from py2many.ast_helpers import get_id
import logging

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler, class_for_typename
from py2many.tracer import find_node_by_type
from pyjl.helpers import get_ann_repr
from pyjl.juliaAst import JuliaNodeVisitor
from pyjl.plugins import JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE, MODULE_DISPATCH_TABLE
import importlib

from numbers import Complex, Integral, Rational, Real
from typing import Any, Dict, List, Optional, Set, Tuple

from ctypes import c_int8, c_int16, c_int32, c_int64
from ctypes import c_uint8, c_uint16, c_uint32, c_uint64

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

_DEFAULT = "Any"
_NONE_TYPE = "nothing"

jl_symbols = {
    ast.BitXor: " ⊻ ", 
    ast.And: " && ", 
    ast.Or: " || ",
    ast.Invert: "~",
    ast.Pow: "^",
    ast.MatMult: "*",
    ast.In: "in",
    ast.NotIn: "not in",
    ast.Eq: "==",
    ast.FloorDiv: "÷"
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
    "bisect"
])

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
    Integral: "Integer",
    complex: "complex",
    Complex: "Complex",
    Rational: "Rational",
    Real: "Real",
    None: "nothing",
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
    Tuple: "Tuple",
    tuple: "Tuple",
    Optional: "nothing",
    bytearray: f"Vector{{Int8}}",
}


def jl_symbol(node):
    """Find the equivalent Julia symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return jl_symbols[symbol_type]

class CLikeTranspiler(CommonCLikeTranspiler, JuliaNodeVisitor):
    def __init__(self):
        super().__init__()
        self._type_map = JULIA_TYPE_MAP
        self._container_type_map = CONTAINER_TYPE_MAP
        self._default_type = _DEFAULT
        self._none_type = _NONE_TYPE
        self._statement_separator = ""
        self._ignored_module_set = IGNORED_MODULE_SET.copy().union(JL_IGNORED_MODULE_SET.copy())
        
    def visit(self, node) -> str:
        if type(node) in jl_symbols:
            return jl_symbol(node)
        else:
            return super().visit(node)

    def visit_Name(self, node) -> str:
        node_id = get_id(node)
        if node_id in julia_keywords:
            return f"{node.id}_"
        
        return super().visit_Name(node)

    def visit_arguments(self, node: ast.arguments) -> Tuple[List[str], List[str]]:
        args = [self.visit(arg) for arg in node.args]
        if args == []:
            return [], []
        typenames, args = map(list, zip(*args))
        # Replace julia keywords
        args = [a if a not in julia_keywords else f"{a}_" for a in args]
        return typenames, args

    def visit_BinOp(self, node) -> str:
        if isinstance(node.op, ast.Mult):
            return "{0}*{1}".format(self.visit(node.left), self.visit(node.right))
        if isinstance(node.op, ast.Pow):
            return "{0}^{1}".format(self.visit(node.left), self.visit(node.right))

        bin_op = f"{self.visit(node.left)} {self.visit(node.op)} {self.visit(node.right)}"
        is_nested = getattr(node, "isnested", None)
        return bin_op if not is_nested else f"({bin_op})"

    def visit_In(self, node) -> str:
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        return f"{left} in {right}"

    def visit_NamedExpr(self, node) -> str:
        return f"({self.visit(node.target)} = {self.visit(node.value)})"

    def visit_keyword(self, node: ast.keyword) -> Any:
        arg_str = node.arg if node.arg not in julia_keywords else f"{node.arg}_"
        return f"{arg_str} = {self.visit(node.value)}"

    ######################################################
    ################### Type Mappings ####################
    ######################################################

    def _map_type(self, typename: str, lifetime=LifeTime.UNKNOWN) -> str:
        typeclass = self._func_for_lookup(typename)
        if typeclass in self._type_map:
            return self._type_map[typeclass]
        elif typeclass in self._container_type_map:
            return self._container_type_map[typeclass]
        elif typeclass in MODULE_DISPATCH_TABLE:
            return MODULE_DISPATCH_TABLE[typeclass]
        else:
            # Default if no type is found
            return typename

    def _typename_from_annotation(self, node, attr="annotation") -> str:
        typename = self._default_type
        if hasattr(node, attr):
            type_node = getattr(node, attr)
            typename = self._typename_from_type_node(type_node)
            if isinstance(type_node, ast.Subscript):
                node.container_type = type_node.container_type
                try:
                    return self._visit_container_type(type_node.container_type)
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
            if node_id.startswith("typing."):
                node_id = node_id.split(".")[1]
            return self._map_type(node_id)
        elif isinstance(node, ast.Subscript):
            (value_type, index_type) = tuple(
                map(lambda x: 
                        get_ann_repr(x, self._map_type, self._none_type), 
                    (node.value, node.slice))
            )
            node.container_type = (value_type, index_type)
            return f"{value_type}{{{index_type}}}"
        return get_ann_repr(node, self._map_type, self._default_type)

    def _combine_value_index(self, value_type, index_type) -> str:
        return f"{value_type}{{{index_type}}}"

    def _visit_container_type(self, typename: Tuple) -> str:
        value_type, index_type = typename
        if isinstance(index_type, List):
            index_type = ", ".join(index_type)
        return self._combine_value_index(value_type, index_type)

    ######################################################
    ################# For Julia Imports ##################
    ######################################################

    def visit_Import(self, node) -> str:
        '''Adds extra function call to _import_str to add 
        Julia import syntax'''

        # Add imports to _imported_names
        names = [self.visit(n) for n in node.names]
        for name, asname in names:
            try:
                imported_name = importlib.import_module(name)
            except ImportError:
                imported_name = name
                
            if asname:
                self._imported_names[asname] = imported_name
            else:
                self._imported_names[name] = imported_name

        imports = []
        for name, alias in names:
            n_import = name.split(".")
            for i in range(len(n_import)):
                if ".".join(n_import[0:i+1]) in self._ignored_module_set:
                    break
                imports.append(self._import_str(name, alias))

        return "\n".join(imports)

    def visit_ImportFrom(self, node) -> str:
        '''Adds to import map even if it is ignored. 
        This ensures that dispatch is correct'''

        imported_name = MODULE_DISPATCH_TABLE[node.module] if node.module in MODULE_DISPATCH_TABLE else node.module
        imported_module = None
        if node.module:
            try:
                imported_module = importlib.import_module(node.module)
            except ImportError:
                pass
        else:
            # Import from '.'
            imported_name = "."

        # Add imports to _imported_names
        names = [self.visit(n) for n in node.names]
        for name, asname in names:
            asname = asname if asname is not None else name
            if imported_module:
                self._imported_names[asname] = getattr(imported_module, name, None)
            else:
                self._imported_names[asname] = (imported_name, name)
        
        if node.module in self._ignored_module_set:
            return ""
        
        names = [n for n, _ in names]
        return self._import_from(imported_name, names, node.level)

    def _import_str(self, name, alias):
        '''Formatting Julia Imports'''

        import_str = self._import(MODULE_DISPATCH_TABLE[name]) if name in MODULE_DISPATCH_TABLE else self._import(name)
        return f"{import_str} as {alias}" if alias else import_str

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

    def _dispatch(self, node, fname: str, vargs: List[str]) -> Optional[str]:
        if isinstance(node, ast.Call) and len(node.args) > 0:
            var = vargs[0]

            # Self argument type lookup
            if var == "self":
                class_node: ast.ClassDef = find_node_by_type(ast.ClassDef, node.scopes)
                for base in class_node.bases:
                    base_str = get_id(base)
                    dispatch_func = self._get_dispatch_func(node, base_str, fname, vargs)
                    if dispatch_func:
                        return dispatch_func

            # Account for JuliaMethodCallRewriter
            if v := node.scopes.find(var):
                annotation = getattr(v, "annotation", None)
                if ann := self._generic_typename_from_type_node(annotation):
                    # Temporary (NOT WORKING)
                    ann: str = re.split(r"\s+[*]", ann)[0]
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
        