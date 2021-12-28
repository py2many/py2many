import ast
from ctypes import c_int64
from pathlib import Path
from build.lib.py2many.exceptions import AstCouldNotInfer, AstTypeNotSupported, TypeNotSupported
from py2many.astx import LifeTime
from typing import Any, Dict, List, Optional, OrderedDict, Tuple, Union
from py2many.ast_helpers import get_id
import logging
from dataclasses import dataclass

from py2many.clike import CLikeTranspiler as CommonCLikeTranspiler
from py2many.tracer import find_in_body, find_node_matching_type
from pyjl.plugins import CONTAINER_TYPE_MAP, MODULE_DISPATCH_TABLE, JULIA_TYPE_MAP, VARIABLE_MAP
import importlib

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

jl_symbols = {ast.BitXor: " ⊻ ", ast.And: " && ", ast.Or: " || "}

def jl_symbol(node):
    """Find the equivalent Julia symbol for a Python ast symbol node"""
    symbol_type = type(node)
    return jl_symbols[symbol_type]

# TODO: Deal with classes in Julia
def class_for_typename(typename, default_type, locals={}) -> Union[str, object]:
    if typename is None:
        return None
    if typename == "super" or typename.startswith("super()"):
        # Cant eval super; causes RuntimeError
        return None
    if typename == "dataclass":
        eval(typename)
    try:
        locals |= VARIABLE_MAP
        typeclass = eval(typename, globals(), locals)
        return typeclass
    except (NameError, SyntaxError, AttributeError, TypeError):
        logger.info(f"could not evaluate {typename}")
        return default_type

class CLikeTranspiler(CommonCLikeTranspiler):
    def __init__(self):
        super().__init__()
        self._type_map = JULIA_TYPE_MAP
        self._default_type = _DEFAULT

    def visit(self, node) -> str:
        if type(node) in jl_symbols:
            return jl_symbol(node)
        else:
            return super().visit(node)

    def visit_Name(self, node) -> str:
        node_id = get_id(node)
        if node_id in julia_keywords:
            return node.id + "_"
        # elif get_id(node) in CONTAINER_TYPE_MAP:
        #     return CONTAINER_TYPE_MAP[get_id(node)]
        return super().visit_Name(node)

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
            if not self.not_inferable(node, type_node) and typename is None:
                raise AstCouldNotInfer(type_node, node)
        return typename

    def not_inferable(self, node, type_node):
        return (
            node is None or
            (isinstance(node, ast.arg))
            # (isinstance(node, ast.arg) and node.arg == "self") 
            or isinstance(type_node, ast.Constant)
        )
    
    def _typename_from_type_node(self, node) -> Union[List, str, None]:
        if isinstance(node, ast.Name):
            return self._map_type(
                get_id(node), getattr(node, "lifetime", LifeTime.UNKNOWN)
            )
        if isinstance(node, ast.Subscript):
            # Store a tuple like (List, int) or (Dict, (str, int)) for container types
            # in node.container_type
            # And return a target specific type
            slice_value = self._slice_value(node) # Check later, for now works
            
            (value_type, index_type) = tuple(
                map(self._typename_from_type_node, (node.value, slice_value))
            )
            if cont_map := self._map_type(value_type):
                value_type = cont_map
            node.container_type = (self._map_type(value_type), self._map_type(index_type))
            return self._combine_value_index(value_type, index_type)
        # If necessary, call super
        super()._typename_from_type_node(node)

    def _map_type(self, typename, lifetime=LifeTime.UNKNOWN) -> str:
        typeclass = class_for_typename(typename, self._default_type)
        if typeclass in JULIA_TYPE_MAP:
            return JULIA_TYPE_MAP[typeclass]
        if typename in CONTAINER_TYPE_MAP:
            return CONTAINER_TYPE_MAP[typename]
        if typename in MODULE_DISPATCH_TABLE:
            return MODULE_DISPATCH_TABLE[typename]
        return typename

    ################################################
    ########### Supporting Julia imports ###########
    ################################################

    def visit_Import(self, node) -> str:
        names = [self.visit(n) for n in node.names]
        
        imports = [
            self._import_str(name, alias) # Does Python inline this?
            for name, alias in names
            if name not in self._ignored_module_set
        ]

        for name, asname in names:
            if asname is not None:
                try:
                    imported_name = importlib.import_module(name)
                except ImportError:
                    imported_name = name
                self._imported_names[asname] = imported_name
        return "\n".join(imports)

    def _import_str(self, name, alias):
        import_str = self._import(MODULE_DISPATCH_TABLE[name]) if name in MODULE_DISPATCH_TABLE else self._import(name)
        return import_str + f" as {alias}" if alias else import_str

    def visit_ImportFrom(self, node) -> str:
        if node.module in self._ignored_module_set:
            return ""

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

        names = [self.visit(n) for n in node.names]
        for name, asname in names:
            asname = asname if asname is not None else name
            if imported_module:
                self._imported_names[asname] = getattr(imported_module, name, None)
            else:
                self._imported_names[asname] = (imported_name, name)
            # self._import_aliases[asname] = name # Added
        names = [n for n, _ in names]
        return self._import_from(imported_name, names, node.level)

    # TODO
    ################################################
    ######### For Type Inference Mechanism #########
    ################################################
    def _dispatch(self, node, fname: str, vargs: List[str]) -> Optional[str]:
        # Account for JuliaMethodCallRewriter 
        if isinstance(node, ast.Call) and len(node.args) > 0:
            var = get_id(node.args[0])
            # Find either function or module
            func_node = find_node_matching_type(ast.FunctionDef, node.scopes)
            if not func_node:
                return super()._dispatch(node, fname, vargs)
            var_map = func_node.var_map
            annotation = var_map[var][1] if (var is not None and var in var_map) else None # Get Python type
            if annotation:
                try:
                    py_type = eval(f"{annotation}.{fname}")
                    ret, node.result_type = (self._func_dispatch_table[py_type] 
                        if py_type in self._func_dispatch_table else None)
                    return ret(self, node, vargs)
                except (IndexError, Exception):
                    return super()._dispatch(node, fname, vargs)

        return super()._dispatch(node, fname, vargs)


    # TODO
    ################################################
    ######### Supporting super class calls #########
    ################################################
    def _func_for_lookup(self, fname) -> Union[str, object]:
        func = class_for_typename(fname, None, self._imported_names)
        if func is None:
            return None
        try:
            hash(func)
        except TypeError:
            # Ignore unhashable, probably instance
            logger.debug(f"{func} is not hashable")
            return None
        return func