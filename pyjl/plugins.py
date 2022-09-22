import argparse
from bisect import bisect, bisect_left, bisect_right
import contextlib
from copyreg import constructor
import importlib
import io
import itertools
import math
import operator
import pathlib
import tempfile
import time
import os
import ast
import random
import re
import sys
import traceback
import bisect

from py2many.exceptions import AstUnsupportedOperation
from py2many.scope import ScopeList
from pyjl.global_vars import RESUMABLE
from pyjl.helpers import get_func_def, pycall_import

from tempfile import NamedTemporaryFile
from typing import Any, Callable, Dict, List, Tuple, Union

from py2many.ast_helpers import get_id

from py2many.tracer import (
    find_node_by_name_and_type,
    find_node_by_type,
    is_class_or_module,
    is_class_type,
)

from pyjl import juliaAst

try:
    from dataclasses import dataclass
except ImportError:
    ArgumentParser = "ArgumentParser"
    ap_dataclass = "ap_dataclass"


class JuliaTranspilerPlugins:
    # =====================================
    # Decorators
    # =====================================
    def visit_jl_dataclass(self, node: ast.ClassDef, decorator):
        self._usings.add("DataClass")

        _, field_repr = JuliaTranspilerPlugins._generic_dataclass_visit(node, decorator)

        # Visit class fields
        fields = "\n".join(
            [node.fields_str, "_initvars = [" + ", ".join(field_repr) + "]\n"]
        )

        # Struct definition
        bases = [self.visit(base) for base in node.jl_bases]
        struct_def = (
            f"mutable struct {node.name} <: {bases[0]}"
            if bases
            else f"mutable struct {node.name}"
        )

        body = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                body.append(self.visit(b))
        body = "\n".join(body)

        if hasattr(node, "constructor"):
            constructor_str = self.visit(constructor)
            return f"""@dataclass {struct_def} begin
                    {fields}
                    {constructor_str}
                end
                {body}
            """

        return f"""
            @dataclass {struct_def} begin
                {fields}
            end
            {body}
        """

    def visit_py_dataclass(self, node: ast.ClassDef, decorator) -> str:
        dataclass_data = JuliaTranspilerPlugins._generic_dataclass_visit(
            node, decorator
        )
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
                st_name = (
                    field_type[8:] if field_type.startswith("Abstract") else field_type
                )
                str_struct_fields.append(
                    f"{field_name}::{field_type}"
                    if is_class_type(field_type, node.scopes)
                    else f"{field_name}::Abstract{field_type}"
                )
                key_vars.append(
                    f"self.{field_name}"
                    if (not is_class_type(st_name, node.scopes))
                    else f"__key(self.{field_name})"
                )
            else:
                str_struct_fields.append(f"{field_name}")
                key_vars.append(f"self.{field_name}")
            attr_vars.append(f"self.{field_name}")

        # Convert into string
        key_vars_str = ", ".join(key_vars)
        attr_vars_str = ", ".join(attr_vars)
        str_struct_fields = ", ".join(str_struct_fields)

        # Visit class body
        body = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                body.append(self.visit(b))

        # Add functions to body
        if d_fields["repr"]:
            # __repr__
            show_args = []
            for key in key_vars:
                show_args.append(f"$({key})")
            # TODO: This should be improved
            body.append(
                f"""
                function Base.show(io::IO, self::{struct_name}) 
                    Base.show(io, \"$(nameof(typeof(self)))({', '.join(show_args)})\")
                end
            """
            )
        if d_fields["eq"]:
            # __eq__
            body.append(
                f"""
                function Base.:(==)(self::{struct_name}, other::{struct_name})::Bool
                    return Base.:(==)(__key(self), __key(other))
                end
            """
            )
        if d_fields["order"]:
            # __lt__, __le__, __gt__, __ge__
            body.append(
                f"""
                Base.isless(self::{struct_name}, other::{struct_name}) = begin
                    return Base.isless(__key(self), __key(other)) 
                end\n
                function Base.:(<=)(self::{struct_name}, other::{struct_name})::Bool
                    return Base.:(<=)(__key(self), __key(other))
                end\n
                function Base.:>(self::{struct_name}, other::{struct_name})::Bool
                    return Base.:>(__key(self), __key(other))
                end\n
                function Base.:(>=)(self::{struct_name}, other::{struct_name})::Bool
                    return Base.:(>=)(__key(self), __key(other))
                end
            """
            )
        if d_fields["unsafe_hash"]:
            if d_fields["eq"]:  # && ismutable
                # __hash__
                body.append(
                    f"""
                function Base.hash(self::{struct_name})
                    return Base.hash(__key(self))
                end
                """
                )

        body.append(
            f"""
                function __key(self::{struct_name})
                    ({key_vars_str})
                end
                """
        )

        body = "\n".join(body)

        bases = [self.visit(base) for base in node.jl_bases]
        struct_def = (
            f"mutable struct {node.name} <: {bases[0]}"
            if bases
            else f"mutable struct {node.name}"
        )

        if getattr(node, "constructor", None):
            constructor_str = self.visit(node.constructor)
            return f"{struct_def}\n{fields}\n{constructor_str}\nend\n{body}"

        return f"{struct_def}\n{fields}\nend\n{body}\n"

    def _generic_dataclass_visit(node, decorator):
        fields = {}
        field_repr = []
        keywords = {
            "init": True,
            "repr": True,
            "eq": True,
            "order": False,
            "unsafe_hash": False,
            "frozen": False,
        }
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
            val = key_map[value] if value in key_map else value
            field_repr.append(f"_{arg}={val}")

        return fields, field_repr

    def visit_JuliaClass(self, node: ast.ClassDef, decorator) -> Any:
        self._usings.add("Classes")
        # Parse bases
        bases = []
        for base in node.jl_bases:
            bases.append(self.visit(base))
        # Build struct definition
        bases_str = ", ".join(bases) if len(bases) <= 1 else f"{{{', '.join(bases)}}}"
        # Parse fields
        fields_str = JuliaTranspilerPlugins._get_node_fields(self, node)
        # Structure definition
        struct_def = (
            f"{node.name} <: {', '.join(bases_str)}" if bases_str else f"{node.name}"
        )
        # Parse body
        body = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                body.append(f"{self.visit(b)}")
        body = "\n".join(body)

        if getattr(node, "constructor", None):
            constructor_str = self.visit(node.constructor)
            return f"@class mutable {struct_def} begin\n{fields_str}\n{constructor_str}\nend\n{body}"

        return f"@class mutable {struct_def} begin\n{fields_str}\nend\n{body}\n"

    def _get_node_fields(self, node: ast.ClassDef):
        fields = []
        fields_str = ""
        if node.jl_bases:
            # Avoid repeating fields of superclasses
            base_class_decs = []
            for b in node.jl_bases:
                b_name = self.visit(b)
                base_class = find_node_by_name_and_type(
                    b_name, ast.ClassDef, node.scopes
                )[0]
                if base_class:
                    base_class_decs.extend(list(map(lambda x: x[0], base_class.fields)))

            for (declaration, typename, _) in node.fields:
                if declaration not in base_class_decs:
                    fields.append((declaration, typename))

            fields_str = list(
                map(lambda x: f"{x[0]}::{x[1]}" if x[1] else x[0], fields)
            )
            fields_str = "\n".join(fields_str) if fields else ""
        else:
            fields_str = node.fields_str
        return fields_str

    def visit_OOPClass(self, node: ast.ClassDef, decorator):
        self._usings.add("ObjectOriented")
        # Parse bases
        bases = []
        for base in node.jl_bases:
            bases.append(self.visit(base))
        # Build struct definition
        bases_str = ", ".join(bases) if len(bases) <= 1 else f"{{{', '.join(bases)}}}"
        struct_def = (
            f"mutable struct {node.name} <: {bases_str}"
            if bases
            else f"mutable struct {node.name}"
        )
        # Get docstring
        docstring = self._get_docstring(node)
        maybe_docstring = f"{docstring}\n" if docstring else ""
        # Get constructor (if present)
        maybe_constructor = (
            f"\n{self.visit(node.constructor)}"
            if getattr(node, "constructor", None)
            else ""
        )
        # Parse body as string
        body = "\n".join(list(map(self.visit, node.body)))
        # Parse fields
        oop_parsed_decs = node.parsed_decorators["oop_class"]
        if (
            oop_parsed_decs
            and "oop_nested_funcs" in oop_parsed_decs
            and oop_parsed_decs["oop_nested_funcs"]
        ):
            return f"""@oodef {struct_def}
                        {maybe_docstring}
                        {node.fields_str}
                        {maybe_constructor}
                        {body}
                    end"""
        return f"""@oodef {struct_def}
                    {maybe_docstring}
                    {node.fields_str}
                    {maybe_constructor}
                end
                {body}\n"""

    def visit_contextmanager(self, node, decorator):
        # Using ContextManager from DataTypesBasic.jl
        self._usings.add("DataTypesBasic")
        # There must be at least one argument
        funcdef = (
            f"{node.name}{node.template}({node.parsed_args}) = @ContextManager function(cont)"
        )
        # Visit function body
        body = "\n".join(self.visit(n) for n in node.body)
        if body == "...":
            body = ""

        return f"""{funcdef}
                res = nothing
                {body}
                res
            end\n"""


    def visit_resumables(self, node, decorator):
        # node.scopes[-2] because node.scopes[-1] is the current function
        scopes = getattr(node, "scopes", None)
        parent = None
        if scopes and len(scopes) >= 2:
            parent = node.scopes[-2]
        if isinstance(parent, ast.FunctionDef):
            raise AstUnsupportedOperation(
                "Cannot use resumable functions when function is nested", node
            )

        self._usings.add("ResumableFunctions")

        funcdef = (
            f"function {node.name}{node.template}({node.parsed_args}){node.return_type}"
        )

        # Visit function body
        body = "\n".join(self.visit(n) for n in node.body)
        if body == "...":
            body = ""

        return f"@resumable {funcdef}\n{body}\nend\n"

    def visit_channels(self, node, decorator):
        funcdef = (
            f"function {node.name}{node.template}({node.parsed_args}){node.return_type}"
        )
        # Visit function body
        body = "\n".join(self.visit(n) for n in node.body)
        if body == "...":
            body = ""
        return f"""{funcdef}
                Channel() do ch_{node.name}
                    {body}
                end
            end\n"""

    def visit_parameterized_struct(self, node: ast.ClassDef, decorator):
        if not isinstance(node, ast.ClassDef):
            raise AstUnsupportedOperation(
                "The 'parameterized' decorator can only be used with classes",
                node
            )
        self._usings.add("Parameters")
        body = "\n".join(list(map(self.visit, node.body)))
        bases = []
        for base in node.jl_bases:
            bases.append(self.visit(base))
        # Build struct definition
        struct_def = f"mutable struct {node.name} <: {', '.join(bases)}" \
            if bases else f"mutable struct {node.name}"

        docstring = self._get_docstring(node)
        maybe_docstring = f"{docstring}\n" if docstring else ""
        maybe_constructor = f"\n{self.visit(node.constructor)}" if getattr(node, "constructor", None) else ""

        return f"@with_kw {struct_def}\n{maybe_docstring}{node.fields_str}{maybe_constructor}\nend\n{body}"

    def visit_parameterized_function(self, node: ast.FunctionDef, decorator):
        funcdef = (
            f"function {node.name}{node.template}({node.parsed_args}){node.return_type}"
        )
        # Visit function body
        body = "\n".join(self.visit(n) for n in node.body)
        if body == "...":
            body = ""
        kw_funcs = []
        if hasattr(node, "args_list"):
            arg_lst = ", ".join([arg.arg for arg in node.args.args])
            for i in range(len(node.args_list) - (len(node.args.defaults) - 1)):
                kw_funcs.append(f"{node.name}({', '.join(node.args_list[:i])};"
                    f"{', '.join(node.args_list[i:])}) = {node.name}({arg_lst})")

        kw_funcs = '\n'.join(kw_funcs)
        return f"{kw_funcs}\n{funcdef}\n{body}\nend\n"

    def visit_offsetArrays(self, node, decorator):
        self._usings.add("OffsetArrays")

    def visit_parameterized_unittest(self, node, decorator):
        self._usings.add("ParameterTests")
        self._usings.add("Test")
        funcdef = (
            f"function {node.name}{node.template}(){node.return_type}"
        )
        # Visit function body
        body = "\n".join([self.visit(n) for n in node.body])
        if body == "...":
            body = ""
        if isinstance(decorator, ast.Call):
            param_names = None
            param_args = decorator.args[1]
            if isinstance(param_args, ast.Constant) and \
                    isinstance(param_args.value, str):
                param_names: str = self.visit(param_args)[1:-1]
                if len(param_names.split(",")) > 1:
                    param_names = f"({param_names})"
            else:
                param_names = self.visit(param_args)
            param_list = self.visit(decorator.args[2])
            return f"""@paramtest \"{node.name}\" begin
                    @given {param_names} ∈ {param_list}
                    {body}
                end
            """
            # return f"{funcdef}\n{assign}\n{parameter_test}\nend\n"
        
        return f"{funcdef}\n{body}\nend\n"

    def visit_staticmethod(self, node, decorator):
        funcdef = (
            f"function {node.name}{node.template}({node.parsed_args}){node.return_type}"
        )
        self_type = node.self_type \
            if (hasattr(node, "self_type") and
                not getattr(node, "_oop_nested_funcs", False)) \
            else None
        self_attr = f"self::{node.self_type}" if self_type else "self"
        self_funcdef = (
            f"function {node.name}{node.template}({self_attr}, {node.parsed_args}){node.return_type}"
        )
        # Visit function body
        func_body = "\n".join([self.visit(n) for n in node.body])
        if func_body == "...":
            func_body = ""
        self_func_body = f"""# Wrapper arround {node.name} to support static methods
            {node.name}({node.parsed_args})"""
        self_func = f"{self_funcdef}\n{self_func_body}\nend\n"
        func_def = f"{funcdef}\n{func_body}\nend\n"
        return f"{self_func}\n{func_def}"

    # def visit_array(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
    #     type_code: str = re.sub(r"\"", "", vargs[0])
    #     if type_code in TYPE_CODE_MAP:
    #         return f"Vector{{{TYPE_CODE_MAP[type_code]}}}"

    ######################################################################
    # =====================================
    # Range
    # =====================================
    def visit_range(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
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

        if step:
            return f"{start}:{step}:{stop}"

        return f"{start}:{stop}"

    # =====================================
    # Builtin Functions
    # =====================================
    def visit_getattr(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        parsed_args = JuliaTranspilerPlugins._parse_attrs(self, node)

        if len(parsed_args) == 3:
            # Cannot remove the quotes from default
            default = self.visit(node.args[-1])
            return f"""(hasfield(typeof({parsed_args[0]}), :{parsed_args[1]}) ? 
                getfield({parsed_args[0]}, :{parsed_args[1]}) : {default})"""
        elif len(parsed_args) == 2:
            return f"getfield({parsed_args[0]}, :{parsed_args[1]})"
        return "getfield"

    def visit_hasattr(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        parsed_args = JuliaTranspilerPlugins._parse_attrs(self, node)
        # ann = self.visit(getattr(node.args[0], "annotation", ast.Name("")))
        if parsed_args[1] == "index":
            # Hacks for impossible things
            return f"isa({parsed_args[0]}, String) && hasmethod(Base.findfirst, (String, String))"
        if len(parsed_args) == 2:
            return f"hasfield(typeof({parsed_args[0]}), :{parsed_args[1]})"
        return "hasfield"

    def _parse_attrs(self, node):
        parsed_args = []
        for arg in node.args:
            if isinstance(arg, ast.Constant):
                parsed_args.append(self.visit_Constant(arg, quotes=False))
            else:
                parsed_args.append(self.visit(arg))
        return parsed_args

    def visit_argument_parser(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        pass

    # =====================================
    # Cast
    # =====================================
    def visit_cast_int(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        if hasattr(node, "args") and node.args:
            if len(node.args) == 1:
                arg_type = self._typename_from_annotation(node.args[0])
                if arg_type and arg_type.startswith("Float"):
                    return f"Int(floor({vargs[0]}))"
                elif arg_type and arg_type.startswith("String"):
                    return f"parse(Int, {vargs[0]})"
                else:
                    return f"convert(Int, {vargs[0]})"
            else:
                # TODO: Working on it
                pass
        return f"zero(Int)"  # Default int value

    def visit_cast_float(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        if len(vargs) > 0:
            arg_typename = self._typename_from_annotation(node.args[0])
            if arg_typename and arg_typename.startswith("String"):
                return f"parse(Float64, {vargs[0]})"
            else:
                return f"float({vargs[0]})"
        return f"zero(Float64)"  # Default float value

    def visit_cast_string(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        if get_id(getattr(node.args[0], "annotation", None)) == "Exception":
            return f"Base.show(stdout, {', '.join(vargs)})"
        return f"string({', '.join(vargs)})"

    # =====================================
    # Math
    # =====================================
    def visit_fsum(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        self._usings.add("Xsum")
        return f"xsum({', '.join(vargs)})"

    # =====================================
    # Conversions
    # =====================================
    def visit_inttobytes(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        # Thanks to Steven G. Johnson for this function
        # https://discourse.julialang.org/t/julia-equivalent-to-pythons-int-to-bytes/44038/9
        func = """function to_bytes(n::Integer; bigendian=true, len=sizeof(n))
           bytes = Array{UInt8}(undef, len)
           for byte in (bigendian ? (1:len) : reverse(1:len))
               bytes[byte] = n & 0xff
               n >>= 8
           end
           return bytes
        end"""
        self._globals.add(func)
        return f"to_bytes({', '.join(vargs[0])})"

    # =====================================
    # String operations
    # =====================================
    def visit_maketrans(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        original_lst = [vargs[0][i] for i in range(2, len(vargs[0]) - 1)]
        replacement_lst = []
        byte_replacements = str(vargs[1][2:-1])
        i = 0
        while i < len(byte_replacements):
            if byte_replacements[i : i + 2] == "\\x":
                replacement_lst.append(str(byte_replacements[i : i + 4]))
                i += 4
            else:
                replacement_lst.append(byte_replacements[i])
                i += 1
        element_lst = []
        for o, r in zip(original_lst, replacement_lst):
            if o in self._str_special_character_map:
                o = self._str_special_character_map[o]
            if r in self._str_special_character_map:
                r = self._str_special_character_map[r]
            element_lst.append(f'b"{o}" => b"{r}"')
        element_lst_str = ", ".join(element_lst)
        return f"Dict({element_lst_str})"

    def visit_join(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        if len(vargs) == 2:
            return f"join({vargs[1]}, {vargs[0]})"
        elif len(vargs) == 1:
            return f"x -> join(x, {vargs[0]})"
        return "join"

    def visit_format(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        if isinstance(node.args[0], ast.Constant):
            subst_values: list[str] = vargs[1:]
            res: str = re.split(r"{|}", vargs[0])
            kw_arg_names = {kwarg[0]: kwarg[1] for kwarg in kwargs}
            # Replace elements in string
            cnt = 0
            for i in range(1, len(res)-1, 2):
                if res[i] == f"{cnt}" or res[i] == "":
                    res[i] = f"$({subst_values[cnt]})"
                elif re.match(r"!r|n", res[i]):
                    res[i] = f"$({subst_values[cnt]})"
                elif res[i] in kw_arg_names:
                    res[i] = kw_arg_names[res[i]]
                cnt += 1
            return "".join(res)
        else:
            # Replace named arguments with positional arguments
            if kwargs:
                count = 1
                replace_str_map = []
                kw_values = []
                for kwarg in kwargs:
                    replace_str_map.append(f"\"{{{kwarg[0]}}}\" => \"{{{count}}}\"")
                    kw_values.append(kwarg[1])
                    count += 1
                replace_func = f"replace({vargs[0]}, {', '.join(replace_str_map)})"
                self._usings.add("Formatting")
                return f"format({replace_func}, {', '.join(kw_values)})"
        self._usings.add("Formatting")
        return f"format({', '.join(vargs)})" \
            if vargs else "format"

    def visit_translate(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        if len(vargs) < 2:
            return "replace!"
        if len(vargs) == 2:
            translation_map = vargs[1]
        elif len(vargs) == 3:
            # Include "delete" parameter
            key_map = []
            del_args = vargs[2][2:-1]
            i = 0
            while i < len(del_args):
                if del_args[i] == "\\":
                    arg = del_args[i : i + 2]
                    i += 2
                else:
                    arg = del_args[i]
                    i += 1
                if arg in self._str_special_character_map:
                    arg = self._str_special_character_map[arg]
                key_map.append(f'b"{arg}" => b""')
            key_map = ", ".join(key_map)
            translation_map = f"merge!({vargs[1]}, Dict({key_map}))"
        return f"replace!(collect({vargs[0]}), {translation_map}...)"

    # =====================================
    # Array Operations
    # =====================================
    def visit_bytearray(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        if len(vargs) == 0:
            return "Vector{UInt8}()"
        else:
            parsed_args = vargs[0]
            if isinstance(node.args[0], ast.GeneratorExp) or getattr(
                node.args[0], "is_gen_expr", None
            ):
                parsed_args = parsed_args.removeprefix("(").removesuffix(")")
                parsed_args = f"[{vargs[0][1:-1]}]"
            return f"Vector{{UInt8}}({parsed_args})"

    def visit_islice(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        node.is_gen_expr = True
        return f"({vargs[0]} for _ in (1:{vargs[1]}))"

    def visit_iter(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        node.is_gen_expr = True
        return f"(x for x in {vargs[0]})"

    def visit_next(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        func_def = get_func_def(node, vargs[0])
        annotation = getattr(func_def, "annotation", ast.Name(""))
        ann_id: str = self.visit(annotation)
        if ann_id == "Generator":
            decs = getattr(func_def, "parsed_decorators", None)
            if RESUMABLE in decs:
                if len(vargs) > 1:
                    return f"{vargs[0]}({', '.join(vargs[1:])})"
                elif getattr(node, "is_attr", None):
                    return f"{vargs[0]}"
                else:
                    return f"{vargs[0]}()"
            else:
                return f"take!({vargs[0]})"

        # TODO: Is this valid? Is this undecidable?
        # else:
        #     getattr(node, "is_gen_expr", None)
        #     return f"(({vargs[0]}, state) = iterate({vargs[0]}, state))"
        return f"next({', '.join(vargs)})"

    def visit_zip(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        ls1 = node.args[0]
        if isinstance(ls1, ast.Constant) and isinstance(ls1.value, str):
            ls1_lst = []
            for n in ls1.value:
                ls1_lst.append(f'"{n}"')
            return f"zip([{', '.join(ls1_lst)}], {vargs[1]})"

        if len(vargs) == 0:
            return "zip"
        if len(vargs) == 1:
            f"zip({vargs[0]})"

        return f"zip({vargs[0]}, {vargs[1]})"

    def visit_frozenset_contains(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        self._usings.add("FunctionalCollections")
        return (
            f"{vargs[1]} in {vargs[0]}" if len(vargs) == 2 else "x::pset, y -> y in x"
        )

    # =====================================
    # Bisection
    # =====================================
    def visit_bisect_right(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        JuliaTranspilerPlugins._generic_bisect_visit(self)
        return f"bisect_right({', '.join(vargs)})" if vargs else "bisect_right"

    def visit_bisect_left(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        JuliaTranspilerPlugins._generic_bisect_visit(self)
        return f"bisect_left({', '.join(vargs)})" if vargs else "bisect_left"

    def _generic_bisect_visit(self):
        self._usings.add("BisectPy")

    # =====================================
    # IO
    # =====================================
    def visit_print(self, node: ast.Call, vargs: List[str], kwargs: list[tuple[str,str]]) -> str:
        if len(vargs) == 0:
            return "println()"
        if len(vargs) == 1 and not kwargs and not isinstance(node.args[0], ast.BinOp):
            return f"println({vargs[0]})"
        parsed_args = []
        args_str, args_vals = [], []
        for node_arg in node.args:
            arg = self.visit(node_arg)
            if arg and arg.startswith('"'):
                arg = arg[1:-1]
            if isinstance(node_arg, ast.BinOp):
                if isinstance(node_arg.op, ast.Mod):
                    args_str.append(self.visit(node_arg.left)[1:-1])
                    args_vals.append(self.visit(node_arg.right))
                    parsed_args.append(arg)
                else:
                    parsed_bin_op = JuliaTranspilerPlugins._parse_bin_op(self, node_arg)
                    parsed_args.append(parsed_bin_op)
            elif isinstance(node_arg, ast.Constant) or isinstance(node_arg, ast.Call):
                parsed_args.append(arg)
            else:
                parsed_args.append(f"$({arg})")

        func_name = "println"
        sep = " "
        end = "\\n"
        flush = False
        print_repr = []
        for k in kwargs:
            if k[0] == "file":
                func_name = "write"
                print_repr.append(k[1])
            elif k[0] == "end":
                end = k[1]
            elif k[0] == "sep":
                sep = k[1]
            elif k[0] == "flush":
                flush = True

        if args_str and not print_repr:
            self._usings.add("Printf")
            return f'@printf("{sep.join(args_str)}{end}", {", ".join(args_vals)})'

        # Append parsed arguments
        print_repr.append(f'"{sep.join(parsed_args)}"')

        maybe_flush = ""
        if flush:
            maybe_flush = (
                f"\nflush({print_repr[0]})"
                if func_name == "write"
                else f"\nflush(stdout)"
            )

        if end != "\\n" and func_name == "println":
            return f"print({', '.join(print_repr)}{end}){maybe_flush}"
        return f"{func_name}({', '.join(print_repr)}){maybe_flush}"

    def _parse_bin_op(self, node: ast.BinOp):
        left: str
        right: str
        if isinstance(node.op, ast.Add):
            # Left node
            if isinstance(node.left, ast.BinOp):
                left = JuliaTranspilerPlugins._parse_bin_op(self, node.left)
            elif isinstance(node.left, ast.Constant):
                left = self.visit_Constant(node.left, quotes=False)
            else:
                left = f"$({self.visit(node.left)})"
            # Right node
            if isinstance(node.right, ast.BinOp):
                right = JuliaTranspilerPlugins._parse_bin_op(self, node.right)
            elif isinstance(node.right, ast.Constant):
                right = self.visit_Constant(node.right, quotes=False)
            else:
                right = f"$({self.visit(node.right)})"
            return f"{left}{right}"
        else:
            return f"$({self.visit(node)})"

    def visit_write(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        if not vargs or getattr(node, "is_attr", False):
            return f"x -> write(stdout, x)"
        return f"write(stdout, {vargs[0]})"

    def visit_flush(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        if not vargs or getattr(node, "is_attr", False):
            return f"flush(stdout)"
        return f"flush({vargs[0]})"

    def visit_textio_read(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        # TODO
        return None

    def visit_textio_write(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        # TODO
        return None

    def visit_encode(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        self._usings.add("StringEncodings")
        if len(vargs) == 0:
            return "encode"
        if len(vargs) == 1:
            return f'encode({self.visit(node.args[0])}, "UTF-8")'
        return f"encode({vargs[0]}, {vargs[1]})"

    def visit_splitlines(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        if vargs:
            if isinstance(node.args[0], ast.Constant) and \
                    isinstance(node.args[0].value, str):
                v0 = node.args[0].value.removesuffix('\n')
                v0 = f"\"{v0}\""
            else:
                v0 = vargs[0].removesuffix('\n')
            return f"split({v0}, r\"\\n|\\r\\n\")"
        return "lambda x: split(x.removesuffix('\n'), r\"\\n|\\r\\n\")"

    def visit_ord(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        v0 = vargs[0].replace('"', "'")
        return f"Int(codepoint({v0}))"

    def visit_open(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        for_node = find_node_by_type(ast.For, node.scopes)
        # Check if this is always like this
        if for_node is not None:
            return f"readline({vargs[0]})"

        return f"open({vargs[0]}, {vargs[1]})"

    def visit_named_temp_file(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        node.annotation = ast.Name(id="tempfile._TemporaryFileWrapper")
        node.result_type = True
        return "NamedTempFile::new()"

    def visit_isinstance(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        is_pycall_import = JuliaTranspilerPlugins._check_pycall_import(self, vargs[1])
        if is_pycall_import:
            return f"pybuiltin(:isinstance)({vargs[0]}, {self._map_type(vargs[1])})"
        elif isinstance(node.args[1], ast.Tuple):
            elts = list(map(lambda x: self._map_type(self.visit(x)), node.args[1].elts))
            return f"isa({vargs[0]}, Union{{{', '.join(elts)}}})"
        return f"isa({vargs[0]}, {self._map_type(vargs[1])})"

    def visit_issubclass(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        is_pycall_import = JuliaTranspilerPlugins._check_pycall_import(self, vargs[1])
        if is_pycall_import:
            return f"pybuiltin(:issubclass)({self._map_type(vargs[0])}, {self._map_type(vargs[1])})"
        return f"{self._map_type(vargs[0])} <: {self._map_type(vargs[1])}"

    def _check_pycall_import(self, name):
        instance = name.split(".")
        is_pycall_import = False
        inst_call = []
        for inst in instance:
            inst_call.append(inst)
            if ".".join(inst_call) in self._pycall_imports:
                is_pycall_import = True
                break
        return is_pycall_import

    # =====================================
    # regex
    # =====================================
    def visit_refindall(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        if len(vargs) == 1:
            return f"""
                # Unsupported use of re.findall with one arg
                findall({vargs[0]})"""
        else:
            vargs[0] = JuliaTranspilerPlugins._replace_regex_val(
                node.args[0], vargs[0], "Regex", "r"
            )
            if len(vargs) == 2:
                return f"collect(eachmatch({vargs[0]}, {vargs[1]}))"
            elif len(vargs) == 3:
                return f"""
                    # Flags unsupported
                    collect(eachmatch(r\"{vargs[0]}\", {vargs[1]}))"""

    def visit_resub(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        if len(vargs) < 3:
            return f"""
                # Unsupported use of re.sub with less than 3 arguments
                sub()"""
        else:
            vargs[0] = JuliaTranspilerPlugins._replace_regex_val(
                node.args[0], vargs[0], "Regex", "r"
            )
            vargs[1] = JuliaTranspilerPlugins._replace_regex_val(
                node.args[1], vargs[1], "SubstitutionString", "s"
            )
            return f"replace({vargs[2]}, {vargs[0]} => {vargs[1]})"

    def _replace_regex_val(arg, varg: str, val1, val2):
        if isinstance(arg, ast.Name):
            varg = f"{val1}({varg})"
        elif isinstance(arg, ast.Constant) and isinstance(arg.value, str):
            varg = f"{val2}{varg}"
        return varg

    # =====================================
    # importlib
    # =====================================
    def visit_import(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]) -> str:
        # Try to split 'path' from 'name'
        path, name = os.path.split(vargs[0])
        return f"@eval @from {path} import Symbol({name})"

    # =====================================
    # path
    # =====================================
    def visit_makedirs(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        parsed_args = []
        # Ignore "exist_ok" parameter
        node_args = node.args if len(node.args) <= 2 else node.args[:2]
        for arg in node_args:
            parsed_args.append(self.visit(arg))
        accepted_keywords = set(["mode"])
        for k in kwargs:
            if k[0] in accepted_keywords:
                parsed_args.append(k[1])
        return f"mkpath({', '.join(parsed_args)})"

    # =====================================
    # random
    # =====================================
    def visit_random(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        self._usings.add("Random")
        return f"rand({', '.join(vargs)})"

    def visit_randomshuffle(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        self._usings.add("Random")
        if vargs:
            return f"shuffle({', '.join(vargs)})"
        return "shuffle"

    def visit_randomseed(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        self._usings.add("Random")
        return f"Random.seed!({','.join(vargs)})"

    # =====================================
    # async
    # =====================================
    @staticmethod
    def visit_asyncio_run(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        return f"block_on({vargs[0]})"

    # =====================================
    # PyCall
    # =====================================
    def visit_tempfile(
        self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]
    ) -> str:
        pycall_import(self, node, "tempfile")

    # =====================================
    # special assignments
    # =====================================
    def visit_all(self, node: ast.Assign, vargs: list[str]) -> str:
        assert isinstance(node.value, ast.List)
        values = []
        for value in node.value.elts:
            values.append(value.value)
        return f"export {', '.join(values)}"

    def visit_exportall(self, node: ast.Assign, vargs: list[str]):
        assert isinstance(node.value, ast.List)
        self._usings.add("Reexport")
        reexports = []
        for value in node.value.elts:
            reexports.append(f"@reexport using .{value.value}")
        return "\n".join(reexports)


class SpecialFunctionsPlugins:
    def visit_init(self, node: ast.FunctionDef):
        # Remove self
        node.args.args = node.args.args[1:]
        is_oop = hasattr(node, "oop")
        arg_ids = set(map(lambda x: x.arg, node.args.args))
        init_rewriter = InitRewriter(arg_ids, is_oop)
        constructor_body = []
        for n in node.body:
            if n_v := init_rewriter.visit(n):
                constructor_body.append(n_v)
        constructor_calls = init_rewriter.constructor_calls

        # Class assignments
        class_node: ast.ClassDef = find_node_by_type(ast.ClassDef, node.scopes)
        for name, value in class_node.class_assignments.items():
            scopes = getattr(value, "scopes", None)
            if scopes and isinstance(scopes[-1], ast.ClassDef):
                arg_node = ast.arg(arg=name)
                if typename := getattr(value, "annotation", None):
                    arg_node.annotation = typename
                node.args.args.append(arg_node)
                node.args.defaults.append(value)

        constructor = None
        if is_oop:
            assignments = [
                ast.Assign(targets=[ast.Name(id=arg)], value=ast.Name(id=arg))
                for arg in class_node.declarations.keys()
            ]
            body = constructor_calls + assignments
            make_block = juliaAst.Block(name="@mk", body=body)
            ast.fix_missing_locations(make_block)
            constructor_body.append(make_block)
            constructor = ast.FunctionDef(
                name="new",
                args=node.args,
                body=constructor_body,
                parsed_decorators={},
                decorator_list=[],
            )
        else:
            struct_name = get_id(class_node)
            has_default = node.args.defaults != []
            if constructor_body or has_default:
                new_args = [ast.arg(arg=key) for key in class_node.declarations.keys()]
                decls = list(map(lambda x: ast.Name(id=x.arg), node.args.args+new_args))
                new_instance = ast.Call(
                    func=ast.Name(id="new"), args=decls, keywords=[], scopes=ScopeList()
                )
                ast.fix_missing_locations(new_instance)
                constructor_body.append(new_instance)
                constructor = juliaAst.Constructor(
                    name=struct_name,
                    args=node.args,
                    body=constructor_body,
                )

        if constructor:
            ast.fix_missing_locations(constructor)
            constructor.scopes = node.scopes
            constructor.parsed_decorators = node.parsed_decorators
            constructor.decorator_list = node.decorator_list
            constructor.is_constructor = True

        # Used to order the struct fields
        class_node.constructor_args = node.args

        return constructor

    def visit_getattr(self, node: ast.FunctionDef):
        docstring_parsed: str = self._get_docstring(node)
        body = [docstring_parsed] if docstring_parsed else []
        body.extend([self.visit(n) for n in node.body])
        body = "\n".join(body)
        # Parse arguments
        args: list[str] = node.parsed_args.split(", ")
        self_arg = args[0].split("::")
        if len(self_arg) == 2:
            self_arg[1] = self_arg[1].removeprefix("Abstract")
            args[0] = "::".join(self_arg)
        property_arg = args[1].split("::")
        property_arg_name = property_arg[0]
        if len(property_arg) == 1:
            args[1] = f"{args[1]}::Symbol"
        parsed_args = ", ".join(args)

        return f"""function Base.getproperty({parsed_args})
                if hasproperty(self, Symbol({property_arg_name}))
                    return Base.getfield(self, Symbol({property_arg_name}))
                end
                {body}
            end"""

    def visit_show(self, node: ast.FunctionDef):
        body = SpecialFunctionsPlugins._parse_body(self, node)
        return f"""function Base.show(io::IO, {node.parsed_args})
                {body}
            end"""
    
    def visit_lt(self, node: ast.FunctionDef):
        body = SpecialFunctionsPlugins._parse_body(self, node)
        return f"""function Base.isless({node.parsed_args})
                {body}
            end"""

    def visit_le(self, node: ast.FunctionDef):
        body = SpecialFunctionsPlugins._parse_body(self, node)
        return f"""function Base.:(<=)({node.parsed_args})
                {body}
            end"""
    
    def visit_gt(self, node: ast.FunctionDef):
        body = SpecialFunctionsPlugins._parse_body(self, node)
        return f"""function Base.:>({node.parsed_args})
                {body}
            end"""
        
    def visit_ge(self, node: ast.FunctionDef):
        body = SpecialFunctionsPlugins._parse_body(self, node)
        return f"""function Base.:(>=)({node.parsed_args})
                {body}
            end"""

    def visit_eq(self, node: ast.FunctionDef):
        body = SpecialFunctionsPlugins._parse_body(self, node)
        return f"""function Base.:(==)({node.parsed_args})
                {body}
            end"""

    def visit_hash(self, node: ast.FunctionDef):
        body = SpecialFunctionsPlugins._parse_body(self, node)
        return f"""function Base.hash({node.parsed_args})
                {body}
            end"""

    def _parse_body(self, node):
        docstring_parsed: str = self._get_docstring(node)
        body = [docstring_parsed] if docstring_parsed else []
        body.extend([self.visit(n) for n in node.body])
        return "\n".join(body)

class InitRewriter(ast.NodeTransformer):
    constructor_calls = []

    def __init__(self, arg_ids, is_oop) -> None:
        super().__init__()
        self.constructor_calls = []
        self.is_self = lambda x: isinstance(x, ast.Attribute) \
            and get_id(x.value) == "self"
        self.arg_ids = arg_ids
        self.is_oop = is_oop

    def visit_Assign(self, node: ast.Assign) -> Any:
        target = node.targets[0]
        if self.is_self(target):
            new_id = get_id(target).split(".")[1:]
            if new_id[0] in self.arg_ids and \
                    get_id(node.value) in self.arg_ids:
                return None
        self.generic_visit(node)
        return node
    
    def visit_AnnAssign(self, node: ast.AnnAssign) -> Any:
        if self.is_self(node.target):
            new_id = get_id(node.target).split(".")[1:]
            if new_id[0] in self.arg_ids and \
                    get_id(node.value) in self.arg_ids:
                return None
        self.generic_visit(node)
        return node

    def visit_Expr(self, node: ast.Expr) -> Any:
        if self.is_oop and \
                isinstance(node.value, ast.Call) and \
                is_class_or_module(get_id(node.value.func), node.scopes):
            self.constructor_calls.append(node)
        return node

    def visit_Attribute(self, node: ast.Attribute) -> Any:
        if get_id(node.value) == "self":
            return ast.Name(id=node.attr)
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
    "d": "Float64",
}

# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs, kwargs: f"string({vargs[0]})" if vargs else f"string()",
    "len": lambda n, vargs, kwargs: f"length({vargs[0]})",
    "enumerate": lambda n, vargs, kwargs: f"enumerate({vargs[0]})",
    # default is false
    "bool": lambda n, vargs, kwargs: f"Bool({vargs[0]})" if vargs else f"false",
    # ::Int64 below is a hack to pass comb_sort.jl. Need a better solution
    # "floor": lambda n, vargs, kwargs: f"floor({vargs[0]})",
    "None": lambda n, vargs, kwargs: f"Nothing",
    "sys.argv": lambda n, vargs, kwargs: "append!([PROGRAM_FILE], ARGS)",
    "os.environ": lambda n, vargs, kwargs: "keys(ENV)",
    "sys.meta_path": lambda node, vargs, kwargs: "Base.LOAD_PATH",
    # Function methods
    "function.__name__": lambda node, vargs, kwargs: f"nameof({vargs[0]})",
    # Special func names
    "__getattr__": lambda node, vargs, kwargs: f"Base.getattribute({', '.join(vargs)})" \
        if vargs else "Base.getattribute",
    "__repr__": lambda node, vargs, kwargs: f"Base.show(stdout, {', '.join(vargs)})" \
        if vargs else "Base.show",
    "__str__": lambda node, vargs, kwargs: f"Base.show(stdout, {', '.join(vargs)})" \
        if vargs else "Base.show",
    "__eq__": lambda node, vargs, kwargs: f"Base.:(==)({', '.join(vargs)})" \
        if vargs else "Base.:(==)",
    "__lt__": lambda node, vargs, kwargs: f"Base.isless({', '.join(vargs)})" \
        if vargs else "Base.isless",
    "__le__": lambda node, vargs, kwargs: f"Base.:(<=)({', '.join(vargs)})" \
        if vargs else "Base.:(<=)",
    "__gt__": lambda node, vargs, kwargs: f"Base.:>({', '.join(vargs)})" \
        if vargs else "Base.:>",
    "__ge__": lambda node, vargs, kwargs: f"Base.:(>=)({', '.join(vargs)})" \
        if vargs else "Base.:(>=)",
    "__hash__": lambda node, vargs, kwargs: f"Base.hash({', '.join(vargs)})" \
        if vargs else "Base.hash",
}

SMALL_USINGS_MAP = {"asyncio.run": "futures::executor::block_on"}

DISPATCH_MAP = {
    "xrange": JuliaTranspilerPlugins.visit_range,
    "print": JuliaTranspilerPlugins.visit_print,
    "int": JuliaTranspilerPlugins.visit_cast_int,
    "str": JuliaTranspilerPlugins.visit_cast_string,
    "float": JuliaTranspilerPlugins.visit_cast_float,
    "join": JuliaTranspilerPlugins.visit_join,
    "format": JuliaTranspilerPlugins.visit_format,
    "__next__": JuliaTranspilerPlugins.visit_next,
    "Generator.__next__": JuliaTranspilerPlugins.visit_next,
    "encode": JuliaTranspilerPlugins.visit_encode,
    # TODO: array.array not supported yet
    # "array.array": JuliaTranspilerPlugins.visit_array
}

MODULE_DISPATCH_TABLE: Dict[str, str] = {
    "dataclass": "DataClass",
    "json": "JSON",
}

DECORATOR_DISPATCH_TABLE = {
    "jl_dataclass": JuliaTranspilerPlugins.visit_jl_dataclass,
    "dataclass": JuliaTranspilerPlugins.visit_py_dataclass,
    "jl_class": JuliaTranspilerPlugins.visit_JuliaClass,
    "contextlib.contextmanager": JuliaTranspilerPlugins.visit_contextmanager,
    "oop_class": JuliaTranspilerPlugins.visit_OOPClass,
    "resumable": JuliaTranspilerPlugins.visit_resumables,
    "channels": JuliaTranspilerPlugins.visit_channels,
    "parameterized": JuliaTranspilerPlugins.visit_parameterized_struct,
    "parameterized_func": JuliaTranspilerPlugins.visit_parameterized_function,
    "offset_arrays": JuliaTranspilerPlugins.visit_offsetArrays,
    "pytest.mark.parametrize": JuliaTranspilerPlugins.visit_parameterized_unittest,
    "staticmethod": JuliaTranspilerPlugins.visit_staticmethod,
}

CLASS_DISPATCH_TABLE = {
    # "dataclass": JuliaTranspilerPlugins.visit_argparse_dataclass,
}

ATTR_DISPATCH_TABLE = {
    "temp_file.name": lambda self, node, value, attr: f"{value}.path()"
}

JULIA_SPECIAL_NAME_TABLE = {"__file__": "@__FILE__"}


FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    # Array Operations
    list.append: (
        lambda self, node, vargs, kwargs: f"push!({vargs[0]}, {vargs[1]})",
        True,
    ),
    list.clear: (lambda self, node, vargs, kwargs: f"empty!({vargs[0]})", True),
    list.remove: (
        lambda self, node, vargs, kwargs: f"deleteat!({vargs[0]}, findfirst(isequal({vargs[1]}), {vargs[0]}))",
        True,
    ),
    list.extend: (
        lambda self, node, vargs, kwargs: f"append!({vargs[0]}, {vargs[1]})",
        True,
    ),
    list.count: (
        lambda self, node, vargs, kwargs: f"count(isequal({vargs[1]}), {vargs[0]})",
        True,
    ),
    list.index: (
        lambda self, node, vargs, kwargs: f"findfirst(isequal({vargs[1]}), {vargs[0]})",
        True,
    ),
    list: (
        lambda self, node, vargs, kwargs: f"Vector()"
        if len(vargs) == 0
        else f"collect({vargs[0]})",
        True,
    ),
    bytearray: (JuliaTranspilerPlugins.visit_bytearray, True),
    slice: (lambda self, node, vargs, kwargs: f"({vargs[0]}:{vargs[1]})", False),
    iter: (JuliaTranspilerPlugins.visit_iter, False),
    next: (JuliaTranspilerPlugins.visit_next, False),
    range: (JuliaTranspilerPlugins.visit_range, False),
    zip: (JuliaTranspilerPlugins.visit_zip, False),
    frozenset.__contains__: (JuliaTranspilerPlugins.visit_frozenset_contains, False),
    tuple: (
        lambda self, node, vargs, kwargs: f"tuple({vargs[0]}...)"
        if isinstance(node.args[0], ast.GeneratorExp)
        else f"tuple({vargs[0]})",
        False,
    ),
    dict.items: (lambda self, node, vargs, kwargs: f"collect({vargs[0]})", True),
    set: (lambda self, node, vargs, kwargs: f"Set({', '.join(vargs)})", True),
    # Math operations
    math.pow: (lambda self, node, vargs, kwargs: f"{vargs[0]}^({vargs[1]})", False),
    math.sin: (lambda self, node, vargs, kwargs: f"sin({vargs[0]})", False),
    math.cos: (lambda self, node, vargs, kwargs: f"cos({vargs[0]})", False),
    math.tan: (lambda self, node, vargs, kwargs: f"tan({vargs[0]})", False),
    math.asin: (lambda self, node, vargs, kwargs: f"asin({vargs[0]})", False),
    math.acos: (lambda self, node, vargs, kwargs: f"acos({vargs[0]})", False),
    math.atan: (lambda self, node, vargs, kwargs: f"atan({vargs[0]})", False),
    math.radians: (lambda self, node, vargs, kwargs: f"deg2rad({vargs[0]})", False),
    math.fsum: (JuliaTranspilerPlugins.visit_fsum, False),
    math.sqrt: (lambda self, node, vargs, kwargs: f"sqrt({vargs[0]})", False),
    math.trunc: (
        lambda self, node, vargs, kwargs: f"trunc({vargs[0]})" if vargs else "trunc",
        False,
    ),
    sum: (lambda self, node, vargs, kwargs: f"sum({', '.join(vargs)})", False),
    round: (
        lambda self, node, vargs, kwargs: f"round({vargs[0]}, digits = {vargs[1]})",
        False,
    ),
    operator.mod: (
        lambda self, node, vargs, kwargs: f"mod({vargs[0]}, {vargs[1]})"
        if vargs
        else "mod",
        True,
    ),
    operator.floordiv: (
        lambda self, node, vargs, kwargs: f"div({vargs[0]}, {vargs[1]})"
        if vargs
        else "div",
        True,
    ),
    int.conjugate: (
        lambda self, node, vargs, kwargs: f"conj({vargs[0]})" if vargs else "conj",
        True,
    ),
    int.to_bytes: (JuliaTranspilerPlugins.visit_inttobytes, True),
    int.real: (lambda self, node, vargs, kwargs: f"real({vargs[0]})", True),
    int.imag: (lambda self, node, vargs, kwargs: f"imag({vargs[0]})", True),
    int.denominator: (lambda self, node, vargs, kwargs: f"denominator({vargs[0]})", True),
    int.numerator: (lambda self, node, vargs, kwargs: f"numerator({vargs[0]})", True),
    float.conjugate: (
        lambda self, node, vargs, kwargs: f"conj({vargs[0]})" if vargs else "conj",
        True,
    ),
    float.real: (lambda self, node, vargs, kwargs: f"real({vargs[0]})", True),
    float.imag: (lambda self, node, vargs, kwargs: f"imag({vargs[0]})", True),
    math.floor: (
        lambda self, node, vargs, kwargs: f"floor(Int, {vargs[0]})"
        if vargs
        else "floor",
        True,
    ),
    divmod: (
        lambda self, node, vargs, kwargs: f"div({vargs[0]})" if vargs else "div",
        True,
    ),  # Fallback
    # io
    argparse.ArgumentParser.parse_args: (
        lambda self, node, vargs, kwargs: "::from_args()",
        False,
    ),
    sys.stdin.read: (
        lambda self, node, vargs, kwargs: f"read(stdin, String)"
        if len(vargs) == 0
        else f"read({vargs[0]}, {vargs[1]})",
        True,
    ),
    sys.stdin.write: (lambda self, node, vargs, kwargs: f"open({vargs[0]})", True),
    sys.stdin.close: (lambda self, node, vargs, kwargs: f"close({vargs[0]})", True),
    sys.exit: (lambda self, node, vargs, kwargs: f"quit({vargs[0]})", True),
    sys.stdout: (lambda self, node, vargs, kwargs: f"stdout", True),
    sys.stdout.buffer.write: (JuliaTranspilerPlugins.visit_write, True),
    sys.stdout.buffer.flush: (JuliaTranspilerPlugins.visit_flush, True),
    open: (JuliaTranspilerPlugins.visit_open, True),
    io.TextIOWrapper.read: (JuliaTranspilerPlugins.visit_textio_read, True),
    io.TextIOWrapper.write: (JuliaTranspilerPlugins.visit_textio_write, True),
    io.BytesIO: (lambda self, node, vargs, kwargs: f"IOBuffer({vargs[0]})", True),
    os.unlink: (
        lambda self, node, vargs, kwargs: f"std::fs::remove_file({vargs[0]})",
        True,
    ),
    NamedTemporaryFile: (JuliaTranspilerPlugins.visit_named_temp_file, True),
    pathlib.Path.cwd: (lambda self, node, vargs, kwargs: "pwd()", True),
    # Instance checks
    isinstance: (
        JuliaTranspilerPlugins.visit_isinstance,
        True,
    ),
    issubclass: (
        JuliaTranspilerPlugins.visit_issubclass,
        True,
    ),
    # Bisect
    bisect.bisect: (JuliaTranspilerPlugins.visit_bisect_right, True),
    bisect_right: (JuliaTranspilerPlugins.visit_bisect_right, True),
    bisect_left: (JuliaTranspilerPlugins.visit_bisect_left, True),
    # Random
    random.random: (JuliaTranspilerPlugins.visit_random, False),
    random.shuffle: (JuliaTranspilerPlugins.visit_randomshuffle, False),
    random.seed: (
        JuliaTranspilerPlugins.visit_randomseed,
        False,
    ),
    # Str and Byte transformations
    str.join: (JuliaTranspilerPlugins.visit_join, False),
    str.format: (JuliaTranspilerPlugins.visit_format, False),
    str.lower: (lambda self, node, vargs, kwargs: f"lowercase({vargs[0]})", True),
    str.upper:  (lambda self, node, vargs, kwargs: f"upercase({vargs[0]})", True),
    str.replace: (lambda self, node, vargs, kwargs: f"replace({vargs[0]}, {vargs[1]} => {vargs[2]})"
        if len(vargs) == 3 else "replace", True),
    str.startswith: (lambda self, node, vargs, kwargs: f"startswith({', '.join(vargs)})", True),
    str.encode: (JuliaTranspilerPlugins.visit_encode, True),
    str.splitlines: (JuliaTranspilerPlugins.visit_splitlines, True),
    bytes.maketrans: (JuliaTranspilerPlugins.visit_maketrans, True),
    bytearray.translate: (JuliaTranspilerPlugins.visit_translate, False),
    bytes.translate: (JuliaTranspilerPlugins.visit_translate, False),
    # Itertools
    itertools.repeat: (
        lambda self, node, vargs, kwargs: f"repeat({vargs[0], vargs[1]})"
        if len(vargs) > 2
        else f"repeat({vargs[0]})",
        False,
    ),
    itertools.islice: (JuliaTranspilerPlugins.visit_islice, True),
    # Time
    time.time: (lambda self, node, vargs, kwargs: "pylib::time()", False),
    # Regex
    re.findall: (JuliaTranspilerPlugins.visit_refindall, False),
    re.sub: (JuliaTranspilerPlugins.visit_resub, False),
    # Memory handling
    contextlib.closing: (
        lambda self, node, vargs, kwargs: vargs[0],
        False,
    ),  # TODO: Just a temporary fix
    # Traceback
    traceback.print_exc: (
        lambda self, node, vargs, kwargs: "current_exceptions() != [] ? "
        "current_exceptions()[end] : nothing",
        False,
    ),
    # builtin functions
    getattr: (JuliaTranspilerPlugins.visit_getattr, False),
    hasattr: (JuliaTranspilerPlugins.visit_hasattr, False),
    setattr: (
        lambda self, node, vargs, kwargs: f"setfield!({vargs[0]}, :{vargs[1]}, {vargs[2]})"
        if vargs
        else "setfield",
        True,
    ),
    chr: (lambda self, node, vargs, kwargs: f"Char({vargs[0]})", False),
    ord: (JuliaTranspilerPlugins.visit_ord, False),
    # Path
    os.path.split: (lambda self, node, vargs, kwargs: f"splitdir({vargs[0]})", False),
    os.path.join: (
        lambda self, node, vargs, kwargs: f"joinpath({', '.join(vargs)})",
        False,
    ),
    os.path.dirname: (
        lambda self, node, vargs, kwargs: f"dirname({', '.join(vargs)})",
        False,
    ),
    os.makedirs: (JuliaTranspilerPlugins.visit_makedirs, False),
    os.remove: (lambda self, node, vargs, kwargs: f"rm({vargs[0]})", False),
    os.unlink: (lambda self, node, vargs, kwargs: f"rm({vargs[0]})", False),
    os.path.isdir: (lambda self, node, vargs, kwargs: f"isdir({vargs[0]})", False),
    os.path.isfile: (lambda self, node, vargs, kwargs: f"isfile({vargs[0]})", False),
    os.path.exists: (
        lambda self, node, vargs, kwargs: f"ispath({vargs[0]})",
        False,
    ),  # TODO: Is this too generic?
    os.path.realpath: (
        lambda self, node, vargs, kwargs: f"realpath({vargs[0]})",
        False,
    ),
    # os (generic)
    os.cpu_count: (lambda self, node, vargs, kwargs: f"length(Sys.cpu_info())", True),
    # importlib
    importlib.import_module: (JuliaTranspilerPlugins.visit_import, False),
    importlib.__import__: (JuliaTranspilerPlugins.visit_import, False),
    # parsing args
    argparse.ArgumentParser: (JuliaTranspilerPlugins.visit_argument_parser, True),
    # sys special calls
    sys.exit: (
        lambda self, node, vargs, kwargs: f"exit({vargs[0]})" if vargs else "exit()",
        True,
    ),
    sys.maxsize: (lambda self, node, vargs, kwargs: "typemax(Int)", True),
    # TODO: Change sys.executable for python.exe path
    sys.executable: (lambda self, node, vargs, kwargs: "joinpath(Base.Sys.BINDIR, Base.julia_exename())", True),
    # calls invoking PyCall
    tempfile.mkdtemp: (JuliaTranspilerPlugins.visit_tempfile, True),
    eval: (lambda self, node, vargs, kwargs: f"py\"{', '.join(vargs)}\"", True),
    exec: (lambda self, node, vargs, kwargs: f"py\"\"\"{', '.join(vargs)}\"\"\"", True),
}


JULIA_SPECIAL_ASSIGNMENT_DISPATCH_TABLE = {
    "__all__": JuliaTranspilerPlugins.visit_all,
    "__exportall__": JuliaTranspilerPlugins.visit_exportall
}

JULIA_SPECIAL_FUNCTIONS = {
    "__getattr__": SpecialFunctionsPlugins.visit_getattr,
    "__repr__": SpecialFunctionsPlugins.visit_show,
    "__str__": SpecialFunctionsPlugins.visit_show,
    "__lt__": SpecialFunctionsPlugins.visit_lt,
    "__le__": SpecialFunctionsPlugins.visit_le,
    "__gt__": SpecialFunctionsPlugins.visit_gt,
    "__ge__": SpecialFunctionsPlugins.visit_ge,
    "__eq__": SpecialFunctionsPlugins.visit_eq,
    "__hash__": SpecialFunctionsPlugins.visit_hash,
}
