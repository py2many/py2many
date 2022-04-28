import argparse
from bisect import bisect, bisect_left, bisect_right
import contextlib
import io
import itertools
import math
from multiprocessing import Pool
import multiprocessing
import operator
import time
import os
import ast
import random
import re
import sys
import unittest
import bisect

from py2many.exceptions import AstUnsupportedOperation
from pyjl.global_vars import RESUMABLE
from pyjl.helpers import get_ann_repr

import pyjl.juliaAst as juliaAst

from tempfile import NamedTemporaryFile
from typing import Any, Callable, Dict, List, Tuple, Union

from py2many.ast_helpers import get_id

from py2many.tracer import find_closest_scope, find_in_body, find_node_by_name, find_node_by_name_and_type, find_node_by_type, get_class_scope, is_class_type

try:
    from dataclasses import dataclass
except ImportError:
    ArgumentParser = "ArgumentParser"
    ap_dataclass = "ap_dataclass"


class JuliaTranspilerPlugins:
    def visit_jl_dataclass(t_self, node: ast.ClassDef, decorator):
        t_self._usings.add("DataClass")

        _, field_repr = JuliaTranspilerPlugins._generic_dataclass_visit(node, decorator)

        # Visit class fields
        fields = "\n".join([
            node.fields_str,
            "_initvars = [" + ", ".join(field_repr) + "]\n"
        ])

        # Struct definition
        bases = [t_self.visit(base) for base in node.jl_bases]
        struct_def = f"mutable struct {node.name} <: {bases[0]}" \
            if bases else f"mutable struct {node.name}"

        body = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                body.append(t_self.visit(b))
        body = "\n".join(body)

        if hasattr(node, "constructor_str"):
            return f"""@dataclass {struct_def} begin
                {fields}
                {node.constructor_str}
            end
            {body}"""

        return f"""
            @dataclass {struct_def} begin
                {fields}
            end
            {body}
        """

    def visit_py_dataclass(t_self, node: ast.ClassDef, decorator) -> str:
        dataclass_data = JuliaTranspilerPlugins._generic_dataclass_visit(node, decorator)
        [d_fields, _] = dataclass_data[0], dataclass_data[1]

        fields: str = node.fields_str
        struct_fields = fields.split("\n") if fields else ""

        # Abstract type
        struct_name = "".join(["Abstract", get_id(node)])

        # get struct variables using getfield
        attr_vars = []
        key_vars = []
        str_struct_fields = []
        for field in struct_fields:
            field_name = field
            field_type = None
            field_split = field.split("::")
            if len(field_split) > 1:
                field_name = field_split[0]
                field_type = field_split[1]

            if field_type:
                st_name = field_type[8:] if field_type.startswith("Abstract") else field_type
                str_struct_fields.append(f"{field_name}::{field_type}"
                                        if is_class_type(field_type, node.scopes)
                                        else f"{field_name}::Abstract{field_type}")  
                key_vars.append(f"self.{field_name}"
                            if (not is_class_type(st_name, node.scopes)) else f"__key(self.{field_name})")
            else:
                str_struct_fields.append(f"{field_name}")
                key_vars.append(f"self.{field_name}")
            attr_vars.append(f"self.{field_name}")   

        # Convert into string
        key_vars = ", ".join(key_vars)
        attr_vars = ", ".join(attr_vars)
        str_struct_fields = ", ".join(str_struct_fields)

        # Visit class body
        body = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                body.append(t_self.visit(b))

        # Add functions to body
        if d_fields["repr"]:
            body.append(f"""
                function __repr__(self::{struct_name})::String 
                    return {struct_name}({attr_vars}) 
                end
            """)
        if d_fields["eq"]:
            body.append(f"""
                function __eq__(self::{struct_name}, other::{struct_name})::Bool
                    return __key(self) == __key(other)
                end
            """)
        if d_fields["order"]:
            body.append(f"""
                function __lt__(self::{struct_name}, other::{struct_name})::Bool
                    return __key(self) < __key(other)
                end\n
                function __le__(self::{struct_name}, other::{struct_name})::Bool
                    return __key(self) <= __key(other)
                end\n
                function __gt__(self::{struct_name}, other::{struct_name})::Bool
                    return __key(self) > __key(other)
                end\n
                function __ge__(self::{struct_name}, other::{struct_name})::Bool
                    return __key(self) >= __key(other)
                end
            """)
        if d_fields["unsafe_hash"]:
            if d_fields["_eq"]:  # && ismutable
                body.append(f"""
                function __hash__(self::{struct_name})
                    return __key(self)
                end
                """)

        body.append(f"""
                function __key(self::{struct_name})
                    ({key_vars})
                end
                """)

        body = "\n".join(body)

        bases = [t_self.visit(base) for base in node.jl_bases]
        struct_def = f"mutable struct {node.name} <: {bases[0]}" \
            if bases else f"mutable struct {node.name}"

        if hasattr(node, "constructor_str"):
            return f"{struct_def}\n{fields}\n{node.constructor_str}\nend\n{body}"

        return f"{struct_def}\n{fields}\nend\n{body}"
        

    def _generic_dataclass_visit(node, decorator):
        fields = {}
        field_repr = []
        keywords = {'init': True, 'repr': True, 'eq': True, 'order': False,
                    'unsafe_hash': False, 'frozen': False}
        parsed_decorators: Dict[str, Dict[str, str]] = node.parsed_decorators

        # Parse received keywords if needed
        if isinstance(decorator, ast.Call):
            parsed_keywords: Dict[str, str] = parsed_decorators[get_id(decorator.func)]
            for (key, value) in parsed_keywords.items():
                keywords[key] = value

        key_map = {False: "false", True: "true"}
        for kw in keywords:
            arg = kw
            value = keywords[arg]
            if value == None:
                return (None, None)
            fields[arg] = value
            field_repr.append(f"_{arg}={key_map[value]}")

        return fields, field_repr

    def visit_JuliaClass(t_self, node: ast.ClassDef, decorator) -> Any:
        t_self._usings.add("Classes")

        # Struct definition
        fields = []
        bases = []
        for b in node.jl_bases:
            b_name = t_self.visit(b)
            if b_name != f"Abstract{node.name}":
                bases.append(b_name)

            # Don't repeat elements of superclasses
            base_class = find_node_by_name_and_type(b_name, ast.ClassDef, node.scopes)[0]
            if base_class:
                base_class_decs = list(map(lambda x: x[0], base_class.fields))
                for (declaration, typename, _) in node.fields:
                    if declaration not in base_class_decs:
                        fields.append((declaration, typename))

        # Change string representation if fields have been changed
        if fields and fields != node.fields:
            fields_str = list(map(lambda x: f"{x[0]}::{x[1]}" if x[1] else x[0], fields))
            node.fields_str = ", ".join(fields_str) if fields else ""

        struct_def = f"{node.name} <: {', '.join(bases)}" \
            if bases else f"{node.name}"

        body = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                body.append(f"{t_self.visit(b)}")
        body = "\n".join(body)

        if hasattr(node, "constructor"):
            return f"@class {struct_def}begin\n{node.fields_str}\n{node.constructor_str}\nend\n{body}"

        return f"@class {struct_def} begin\n{node.fields_str}\nend\n{body}"

    def visit_resumables(t_self, node, decorator):
        # node.scopes[-2] because node.scopes[-1] is the current function
        parent = node.scopes[-2]
        if isinstance(parent, ast.FunctionDef):
            raise AstUnsupportedOperation(
                "Cannot use resumable functions when function is nested", node)

        t_self._usings.add("ResumableFunctions")
        
        funcdef = f"function {node.name}{node.template}({node.parsed_args}){node.return_type}"

        # Visit function body
        body = "\n".join(t_self.visit(n) for n in node.body)
        if body == "...":
            body = ""

        maybe_main = "\nmain()" if node.is_python_main else ""
        return f"@resumable {funcdef}\n{body}\nend\n{maybe_main}"

    def visit_offsetArrays(t_self, node, decorator):
        t_self._usings.add("OffsetArrays")

    def visit_async_ann(self, node, decorator):
        return ""

    def visit_assertTrue(t_self, node, vargs):
        JuliaTranspilerPlugins._generic_test_visit(t_self)
        return f"@test {vargs[1]}"

    def visit_assertFalse(t_self, node, vargs):
        JuliaTranspilerPlugins._generic_test_visit(t_self)
        return f"@test !({vargs[1]})"

    def visit_assertEqual(t_self, node, vargs):
        JuliaTranspilerPlugins._generic_test_visit(t_self)
        arg = t_self.visit(ast.Name(id=vargs[2]))
        return f"@test ({vargs[1]} == {arg})"

    def visit_assertRaises(t_self, node, vargs):
        exception = vargs[1]
        func = vargs[2]
        values = ", ".join(vargs[3:])
        return f"@test_throws {exception} {func}({values})"

    def _generic_test_visit(t_self):
        t_self._usings.add("Test")

    # def visit_array(self, node, vargs):
    #     type_code: str = re.sub(r"\"", "", vargs[0])
    #     if type_code in TYPE_CODE_MAP:
    #         return f"Vector{{{TYPE_CODE_MAP[type_code]}}}"

    def visit_open(t_self, node, vargs):
        for_node = find_node_by_type(ast.For, node.scopes)
        # Check if this is always like this
        if for_node is not None:
            return f"readline({vargs[0]})"

        return f"open({vargs[0]}, {vargs[1]})"

    def visit_named_temp_file(t_self, node, vargs):
        node.annotation = ast.Name(id="tempfile._TemporaryFileWrapper")
        node.result_type = True
        return "NamedTempFile::new()"

    def visit_range(t_self, node, vargs: List[str]) -> str:
        # is_number = lambda x: ((isinstance(x, str) 
        #                             and x.lstrip("-").isnumeric())
        #                         or isinstance(x, int))

        start = 0
        stop = 0
        step = None
        if len(vargs) == 1:
            stop = vargs[0]
        else:
            start = vargs[0]
            stop = vargs[1]
            if len(node.args) == 3:
                step = vargs[2]

        # if getattr(node, "range_optimization", False) and \
        #         not getattr(node, "using_offset_arrays", False):
        #     if is_number(start):
        #         start = int(start) + 1
        #     else:
        #         start = f"{start} + 1"
        # else:
        #     if is_number(stop):
        #         stop = int(stop) - 1
        #     else:
        #         stop = f"{stop} - 1"

        if step:
            # if step == "-1":
            #     # Fails with negative indices other than -1 
            #     return f"{stop}:{step}:{start}"
            return f"{start}:{step}:{stop}"

        return f"{start}:{stop}"


    def visit_print(t_self, node: ast.Call, vargs: List[str]) -> str:
        # Revisit
        if node.args:
            if isinstance(node.args[0], ast.BinOp):
                args_str, args_vals = [], []
                for arg in vargs:
                    arg_str, arg_val = re.split(r"\s\%\s", arg)
                    args_str.append(arg_str)
                    args_vals.append(arg_val)

                t_self._usings.add("Printf")
                return f'@printf({", ".join(args_str)}, {", ".join(args_vals)})'

        return f"println({', '.join(vargs)})"

    def visit_cast_int(t_self, node, vargs) -> str:
        if hasattr(node, "args") and node.args:
            needs_parsing = False
            is_float = False
            for arg in node.args:
                arg_type = t_self._typename_from_annotation(arg)
                if arg_type is not None and arg_type.startswith("Float"):
                    is_float = True
                elif not arg_type.startswith("Int"):
                    needs_parsing = True
                    break

            if needs_parsing:
                return f"parse(Int, {vargs[0]})"
            elif is_float:
                return f"Int(floor({vargs[0]}))"
            else:
                return f"Int({vargs[0]})"
        return f"zero(Int)"  # Default int value

    def visit_maketrans(t_self, node, vargs: list[str]):
        original_lst = [vargs[0][i] for i in range(2, len(vargs[0]) - 1)]
        replacement_lst = [vargs[1][i] for i in range(2, len(vargs[1]) - 1)]
        element_lst = []
        for o, r in zip(original_lst, replacement_lst):
            if o in t_self._special_character_map:
                o = t_self._special_character_map[o]
            if r in t_self._special_character_map:
                r = t_self._special_character_map[r]
            element_lst.append(f'b"{o}" => b"{r}"')
        element_lst_str = ", ".join(element_lst)
        return f"Dict({element_lst_str})"

    def visit_starmap(t_self, node, vargs):
        JuliaTranspilerPlugins._generic_distributed_visit(t_self)
        return f"pmap({vargs[1]}, {vargs[2]})"

    def visit_map(t_self, node, vargs):
        JuliaTranspilerPlugins._generic_distributed_visit(t_self)
        return f"pmap({vargs[1]}, {vargs[2]})"

    def visit_Pool(t_self, node, vargs):
        JuliaTranspilerPlugins._generic_distributed_visit(t_self)
        return "default_worker_pool()"
    
    def _generic_distributed_visit(t_self):
        t_self._usings.add("Distributed")

    def visit_join(t_self, node, vargs):
        if len(vargs) == 2:
            return f"join({vargs[1]}, {vargs[0]})"
        elif len(vargs) == 1:
            return f"x -> join(x, {vargs[0]})" 
        return "join"

    def visit_format(t_self, node, vargs):
        # TODO: Optimize
        res: str = vargs[0]
        subst_values = vargs[1:]
        # re.sub(r"\{\d+\}", r"\$" + re.escape(subst_values[r"\d"]), res)
        for i in range(len(subst_values)):
            subst_val = subst_values[i]
            res = res.replace(f"{{{i}}}", f"${subst_val}")
        return res

    def visit_bytearray(t_self, node, vargs: list[str]):
        if len(vargs) == 0:
            return "Vector{UInt8}()"
        else:
            parsed_args = vargs[0]
            if isinstance(node.args[0], ast.GeneratorExp) \
                    or getattr(node.args[0], "is_gen_expr", None):
                parsed_args = parsed_args.removeprefix("(").removesuffix(")")
                parsed_args = f"[{vargs[0][1:-1]}]"
            return f"Vector{{UInt8}}({parsed_args})"

    def visit_islice(t_self, node, vargs: list[str]) -> str:
        node.is_gen_expr = True
        return f"({vargs[0]} for _ in (0:{vargs[1]}))"

    def visit_iter(t_self, node, vargs: list[str]) -> str:
        node.is_gen_expr = True
        return f"(x for x in {vargs[0]})"

    def visit_next(t_self, node: ast.Call, vargs: list[str]) -> str:
        varg = node.scopes.find(vargs[0])
        annotation = get_id(getattr(varg, "annotation", None))

        if annotation == "Generator":
            func_scope = None
            v_node = find_node_by_name(get_id(varg), node.scopes)
            if isinstance(v_node, ast.Assign) and isinstance(v_node.value, ast.Call):
                func_scope = node.scopes.find(get_id(v_node.value.func))
            if func_scope:
                decs = getattr(func_scope, "parsed_decorators", None)
                if RESUMABLE in decs:
                    return f"{vargs[0]}({', '.split(vargs[1:])})" \
                        if len(vargs) > 1 \
                        else f"{vargs[0]}"
                else:
                    return f"take!({vargs[0]})"
        # TODO: Is this valid? Is this undecidable?
        # else:
        #     getattr(node, "is_gen_expr", None)
        #     return f"(({vargs[0]}, state) = iterate({vargs[0]}, state))"
        return f"next({', '.join(vargs)})"

    def visit_zip(t_self, node, vargs: list[str]):
        ls1 = node.args[0]
        if isinstance(ls1, ast.Constant) and \
                isinstance(ls1.value, str):
            ls1_lst = []
            for n in ls1.value:
                ls1_lst.append(f'\"{n}\"')
            return f"zip([{', '.join(ls1_lst)}], {vargs[1]})"
        
        if len(vargs) == 0:
            return "zip"
        if len(vargs) == 1:
            f"zip({vargs[0]})"

        return f"zip({vargs[0]}, {vargs[1]})"

    def visit_bisect_right(t_self, node, vargs: list[str]):
        JuliaTranspilerPlugins._generic_bisect_visit(t_self)
        return f"bisect_right({', '.join(vargs)})" if vargs else "bisect_right"

    def visit_bisect_left(t_self, node, vargs: list[str]):
        JuliaTranspilerPlugins._generic_bisect_visit(t_self)
        return f"bisect_left({', '.join(vargs)})" if vargs else "bisect_left"

    def _generic_bisect_visit(t_self):
        t_self._usings.add("BisectPy")

    def visit_write(t_self, node, vargs: list[str]):
        func_name = JuliaTranspilerPlugins._handle_base_funcs(node, "write")

        if not vargs:
            # TODO: Is there a better way to name the variable?
            return f"x -> {func_name}(stdout, x)"
        return f"{func_name}(stdout, {vargs[0]})"

    def visit_flush(t_self, node, vargs: list[str]):
        func_name = JuliaTranspilerPlugins._handle_base_funcs(node, "flush")

        if not vargs:
            return f"{func_name}(stdout)"
        return f"{func_name}({vargs[0]})"        

    def _handle_base_funcs(node, func_name):
        new_func_name = func_name
        # Searches for a variable with the functions name
        if node.scopes.find(func_name):
            new_func_name = f"Base.{func_name}"
        return new_func_name

    @staticmethod
    def visit_asyncio_run(t_self, node, vargs) -> str:
        return f"block_on({vargs[0]})"

    def visit_textio_read(t_self, node, vargs):
        # TODO
        return None

    def visit_textio_write(t_self, node, vargs):
        # TODO
        return None

    def visit_ap_dataclass(t_self, cls):
        # Do whatever transformation the decorator does to cls here
        return cls


class JuliaRewriterPlugins:
    def visit_init(t_self, node: ast.FunctionDef):
        # Visit Args
        arg_values = JuliaRewriterPlugins._get_args(t_self, node.args)
        for (name, type, default) in arg_values:
            if name not in t_self._class_fields and default:
                # TODO: Deal with linenumber (and col_offset)
                if type:
                    t_self._class_fields[name] = ast.AnnAssign(
                        target=ast.Name(id=name, ctx=ast.Store()),
                        annotation = type,
                        value = default,
                        lineno=1)
                else:
                    t_self._class_fields[name] = ast.Assign(
                        targets=[ast.Name(id=name, ctx=ast.Store())],
                        value = default,
                        lineno=1)

        constructor_body = []
        for n in node.body:
            if not (isinstance(n, ast.Assign) or isinstance(n, ast.AnnAssign)):
                constructor_body.append(n)
            t_self.visit(n)

        if constructor_body:
            parent: ast.ClassDef = node.scopes[-2]
            constructor_args = node.args
            # Remove self
            constructor_args.args = constructor_args.args[1:]
            # TODO: Check lineno and col_offset
            parent.constructor = juliaAst.Constructor(
                                    struct_name = ast.Name(id = parent.name),
                                    args=constructor_args,
                                    body = constructor_body,
                                    ctx=ast.Load(), 
                                    lineno=node.lineno + len(constructor_args.args), 
                                    col_offset=4)

    def _get_args(t_self, args: ast.arguments):
        defaults = args.defaults
        arguments: list[ast.arg] = args.args
        len_defaults = len(defaults)
        len_args = len(arguments)
        arg_values = []
        for i in range(len_args):
            arg = arguments[i]
            default = None
            if defaults:
                if len_defaults != len_args:
                    diff_len = len_args - len_defaults
                    default = defaults[i - diff_len] if i >= diff_len else None
                else:
                    default = defaults[i]
            arg_values.append((arg.arg, arg.annotation, default))

        return arg_values

    def visit_next(r_self, node: ast.FunctionDef):
        r_self.generic_visit(node)
        return node


TYPE_CODE_MAP = {
    "u": "Char",
    "b": "Int8",
    "B": "Uint8",
    "h": "Int16",
    "H": "UInt16",
    "i": "Int32",
    "I": "UInt32",
    "l": "Int64",
    "L": "UInt64",
    "q": "Int128",
    "Q": "UInt128",
    "f": "Float64",
    "d": "Float64"
}

# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda node, vargs: f"string({vargs[0]})" if vargs else f"string()",
    "len": lambda n, vargs: f"length({vargs[0]})",
    "enumerate": lambda n, vargs: f"enumerate({vargs[0]})",
    # default is false
    "bool": lambda n, vargs: f"Bool({vargs[0]})" if vargs else f"false",
    # ::Int64 below is a hack to pass comb_sort.jl. Need a better solution
    # "floor": lambda n, vargs: f"floor({vargs[0]})",
    "None": lambda n, vargs: f"nothing",
    "sys.argv": lambda n, vargs: "append!([PROGRAM_FILE], ARGS)",
    "encode": lambda n, vargs: f"Vector{{UInt8}}({vargs[0]})"
}

SMALL_USINGS_MAP = {
    "asyncio.run": "futures::executor::block_on",
}

DISPATCH_MAP = {
    "xrange": JuliaTranspilerPlugins.visit_range,
    "print": JuliaTranspilerPlugins.visit_print,
    "int": JuliaTranspilerPlugins.visit_cast_int,
    "join": JuliaTranspilerPlugins.visit_join,
    "format": JuliaTranspilerPlugins.visit_format,
    "__next__": JuliaTranspilerPlugins.visit_next,
    # TODO: array.array not supported yet
    # "array.array": JuliaTranspilerPlugins.visit_array
}

MODULE_DISPATCH_TABLE: Dict[str, str] = {
    "dataclass": "DataClass",
    "json": "JSON",
    "datetime": "Dates",
}

DECORATOR_DISPATCH_TABLE = {
    "jl_dataclass": JuliaTranspilerPlugins.visit_jl_dataclass,
    "dataclass": JuliaTranspilerPlugins.visit_py_dataclass,
    "jl_class": JuliaTranspilerPlugins.visit_JuliaClass,
    "resumable": JuliaTranspilerPlugins.visit_resumables,
    "offset_arrays": JuliaTranspilerPlugins.visit_offsetArrays
}

CLASS_DISPATCH_TABLE = {
    # "dataclass": JuliaTranspilerPlugins.visit_argparse_dataclass,
}

ATTR_DISPATCH_TABLE = {
    "temp_file.name": lambda self, node, value, attr: f"{value}.path()",
}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    # Array Operations
    list.append: (lambda self, node, vargs: f"push!({vargs[0]}, {vargs[1]})", True),
    list.clear: (lambda self, node, vargs: f"empty!({vargs[0]})", True),
    list.remove: (lambda self, node, vargs: \
                  f"deleteat!({vargs[0]}, findfirst(isequal({vargs[1]}), {vargs[0]}))", True),
    list.extend: (lambda self, node, vargs: f"append!({vargs[0]}, {vargs[1]})", True),
    list.count: (lambda self, node, vargs: f"count(isequal({vargs[1]}), {vargs[0]})", True),
    list.index: (lambda self, node, vargs: f"findfirst(isequal({vargs[1]}), {vargs[0]})", True),
    list: (lambda self, node, vargs: f"Vector()" if len(vargs) == 0 else f"collect({vargs[0]})", True),
    bytearray: (JuliaTranspilerPlugins.visit_bytearray, True),
    slice: (lambda self, node, vargs: f"({vargs[0]}:{vargs[1]})", False),
    iter: (JuliaTranspilerPlugins.visit_iter, False),
    next: (JuliaTranspilerPlugins.visit_next, False),
    range: (JuliaTranspilerPlugins.visit_range, False),
    zip: (JuliaTranspilerPlugins.visit_zip, False),
    # Math operations
    math.pow: (lambda self, node, vargs: f"{vargs[0]}^({vargs[1]})", False),
    math.sin: (lambda self, node, vargs: f"sin({vargs[0]})", False),
    math.cos: (lambda self, node, vargs: f"cos({vargs[0]})", False),
    math.tan: (lambda self, node, vargs: f"tan({vargs[0]})", False),
    math.asin: (lambda self, node, vargs: f"asin({vargs[0]})", False),
    math.acos: (lambda self, node, vargs: f"acos({vargs[0]})", False),
    math.atan: (lambda self, node, vargs: f"atan({vargs[0]})", False),
    math.radians: (lambda self, node, vargs: f"deg2rad({vargs[0]})", False),
    math.fsum: (lambda self, node, vargs: f"fsum({', '.join(vargs)})", False),
    math.sqrt: (lambda self, node, vargs: f"√({vargs[0]})", False),
    math.trunc: (lambda self, node, vargs: f"trunc({vargs[0]})" if vargs else "trunc", False),
    sum: (lambda self, node, vargs: f"sum({', '.join(vargs)})", False),
    round: (lambda self, node, vargs: f"round({vargs[0]}, digits = {vargs[1]})", False),
    operator.mod: (lambda self, node, vargs: f"mod({vargs[0]}, {vargs[1]})" if vargs else "mod", True),
    operator.floordiv: (lambda self, node, vargs: f"div({vargs[0]}, {vargs[1]})" if vargs else "div", True),
    int.conjugate: (lambda self, node, vargs: f"conj({vargs[0]})" if vargs else "conj", True),
    float.conjugate: (lambda self, node, vargs: f"conj({vargs[0]})" if vargs else "conj", True),
    math.floor:  (lambda self, node, vargs: f"floor(Int, {vargs[0]})" if vargs else "floor", True),
    divmod: (lambda self, node, vargs: f"div({vargs[0]})" if vargs else "div", True), # Fallback
    # io
    argparse.ArgumentParser.parse_args: (lambda self, node, vargs: "::from_args()", False),
    sys.stdin.read: (lambda self, node, vargs: f"open({vargs[0]}, r)", True),
    sys.stdin.write: (lambda self, node, vargs: f"open({vargs[0]})", True),
    sys.stdin.close: (lambda self, node, vargs: f"close({vargs[0]})", True),
    sys.exit: (lambda self, node, vargs: f"quit({vargs[0]})", True),
    sys.stdout.buffer.write: (JuliaTranspilerPlugins.visit_write, True),
    sys.stdout.buffer.flush: (JuliaTranspilerPlugins.visit_flush, True),
    open: (JuliaTranspilerPlugins.visit_open, True),
    io.TextIOWrapper.read: (JuliaTranspilerPlugins.visit_textio_read, True),
    io.TextIOWrapper.read: (JuliaTranspilerPlugins.visit_textio_write, True),
    os.unlink: (lambda self, node, vargs: f"std::fs::remove_file({vargs[0]})", True),
    NamedTemporaryFile: (JuliaTranspilerPlugins.visit_named_temp_file, True),
    # Instance checks
    isinstance: (lambda self, node, vargs: f"isa({vargs[0]}, {vargs[1]})", True),
    issubclass: (lambda self, node, vargs: f"{self._map_type(vargs[0])} <: {self._map_type(vargs[1])}", True),
    # Bisect
    bisect.bisect: (JuliaTranspilerPlugins.visit_bisect_right, True),
    bisect_right: (JuliaTranspilerPlugins.visit_bisect_right, True),
    bisect_left: (JuliaTranspilerPlugins.visit_bisect_left, True),
    # Random
    random.seed: (
        lambda self, node, vargs: f"pylib::random::reseed_from_f64({vargs[0]})",
        False,
    ),
    random.random: (lambda self, node, vargs: "pylib::random::random()", False),
    # Str and Byte transformations
    str.join: (JuliaTranspilerPlugins.visit_join, False),
    str.format: (lambda self, node, vargs: f"test", False),  # Does not work
    bytes.maketrans: (JuliaTranspilerPlugins.visit_maketrans, True),
    "translate": (lambda self, node, vargs: f"replace!({vargs[1]}, {vargs[2]})", False),
    # Itertools
    itertools.repeat: (lambda self, node, vargs: f"repeat({vargs[0], vargs[1]})"
        if len(vargs) > 2 else f"repeat({vargs[0]})", False),
    itertools.islice: (JuliaTranspilerPlugins.visit_islice, True),
    # Multiprocessing
    os.cpu_count: (lambda self, node, vargs: f"length(Sys.cpu_info())", True),
    multiprocessing.cpu_count: (lambda self, node, vargs: f"length(Sys.cpu_info())", True),
    multiprocessing.Pool: (JuliaTranspilerPlugins.visit_Pool, True),
    "starmap": (JuliaTranspilerPlugins.visit_starmap, True), # TODO: remove string-based fallback
    Pool().map: (JuliaTranspilerPlugins.visit_map, True), # TODO: Does not work, Pool is an instance
    # Time
    time.time: (lambda self, node, vargs: "pylib::time()", False),
    # Regex
    re.sub: (lambda self, node, vargs: f"replace({vargs[2]}, r{vargs[0]} => s{vargs[1]})", False),
    re.findall: (lambda self, node, vargs: f"findall({vargs[0]}, {vargs[1]})", False),
    # Unit Tests
    unittest.TestCase.assertTrue: (JuliaTranspilerPlugins.visit_assertTrue, True),
    unittest.TestCase.assertFalse: (JuliaTranspilerPlugins.visit_assertFalse, True),
    unittest.TestCase.assertEqual: (JuliaTranspilerPlugins.visit_assertEqual, True),
    unittest.TestCase.assertRaises: (JuliaTranspilerPlugins.visit_assertRaises, True),
    # Memory handling
    contextlib.closing: (lambda self, node, vargs: vargs[0], False), #TODO: Is this correct
}

# Dispatches special Functions
JULIA_SPECIAL_FUNCTION_DISPATCH_TABLE = {
    "__init__": JuliaRewriterPlugins.visit_init,
    "__next__": JuliaRewriterPlugins.visit_next,
}
