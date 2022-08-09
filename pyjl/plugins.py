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
import time
import os
import ast
import random
import re
import sys
import traceback
import bisect
from py2many.declaration_extractor import DeclarationExtractor

from py2many.exceptions import AstUnsupportedOperation
from py2many.scope import ScopeList
from pyjl.global_vars import RESUMABLE
from pyjl.helpers import get_func_def

from tempfile import NamedTemporaryFile
from typing import Any, Callable, Dict, List, Tuple, Union

from py2many.ast_helpers import get_id

from py2many.tracer import find_node_by_name_and_type, find_node_by_type, is_class_or_module, is_class_type

from pyjl import juliaAst

try:
    from dataclasses import dataclass
except ImportError:
    ArgumentParser = "ArgumentParser"
    ap_dataclass = "ap_dataclass"


class JuliaTranspilerPlugins:
    ########## Decorators ##########
    def visit_jl_dataclass(self, node: ast.ClassDef, decorator):
        self._usings.add("DataClass")

        _, field_repr = JuliaTranspilerPlugins._generic_dataclass_visit(node, decorator)

        # Visit class fields
        fields = "\n".join([
            node.fields_str,
            "_initvars = [" + ", ".join(field_repr) + "]\n"
        ])

        # Struct definition
        bases = [self.visit(base) for base in node.jl_bases]
        struct_def = f"mutable struct {node.name} <: {bases[0]}" \
            if bases else f"mutable struct {node.name}"

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
            {body}"""

        return f"""
            @dataclass {struct_def} begin
                {fields}
            end
            {body}
        """

    def visit_py_dataclass(self, node: ast.ClassDef, decorator) -> str:
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
                body.append(self.visit(b))

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
            if d_fields["eq"]:  # && ismutable
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

        bases = [self.visit(base) for base in node.jl_bases]
        struct_def = f"mutable struct {node.name} <: {bases[0]}" \
            if bases else f"mutable struct {node.name}"

        if getattr(node, "constructor", None):
            constructor_str = self.visit(node.constructor)
            return f"{struct_def}\n{fields}\n{constructor_str}\nend\n{body}"

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
        bases_str = ', '.join(bases) if len(bases) <= 1 else f"{{{', '.join(bases)}}}"
        # Parse fields
        fields_str = JuliaTranspilerPlugins._get_node_fields(self, node)
        # Structure definition
        struct_def = f"{node.name} <: {', '.join(bases_str)}" \
            if bases_str else f"{node.name}"
        # Parse body
        body = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                body.append(f"{self.visit(b)}")
        body = "\n".join(body)

        if getattr(node, "constructor", None):
            constructor_str = self.visit(node.constructor)
            return f"@class mutable {struct_def} begin\n{fields_str}\n{constructor_str}\nend\n{body}"

        return f"@class mutable {struct_def} begin\n{fields_str}\nend\n{body}"

    def _get_node_fields(self, node: ast.ClassDef):
        fields = []
        fields_str = ""
        if node.jl_bases:
            # Avoid repeating fields of superclasses
            base_class_decs = []
            for b in node.jl_bases:
                b_name = self.visit(b)
                base_class = find_node_by_name_and_type(b_name, ast.ClassDef, node.scopes)[0]
                if base_class:
                    base_class_decs.extend(list(map(lambda x: x[0], base_class.fields)))
            
            for (declaration, typename, _) in node.fields:
                if declaration not in base_class_decs:
                    fields.append((declaration, typename))

            fields_str = list(map(lambda x: f"{x[0]}::{x[1]}" if x[1] else x[0], fields))
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
        bases_str = ', '.join(bases) if len(bases) <= 1 else f"{{{', '.join(bases)}}}"
        struct_def = f"mutable struct {node.name} <: {bases_str}" \
            if bases else f"mutable struct {node.name}"
        # Get docstring
        docstring = self._get_docstring(node)
        maybe_docstring = f"{docstring}\n" if docstring else ""
        # Get constructor (if present)
        maybe_constructor = f"\n{self.visit(node.constructor)}" if getattr(node, "constructor", None) else ""
        # Parse body as string
        body = "\n".join(list(map(self.visit, node.body)))
        # Parse fields
        oop_parsed_decs = node.parsed_decorators["oop_class"]
        if oop_parsed_decs and "oop_nested_funcs" in oop_parsed_decs and \
                oop_parsed_decs["oop_nested_funcs"]:
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
                {body}"""

    def visit_resumables(self, node, decorator):
        # node.scopes[-2] because node.scopes[-1] is the current function
        parent = node.scopes[-2]
        if isinstance(parent, ast.FunctionDef):
            raise AstUnsupportedOperation(
                "Cannot use resumable functions when function is nested", node)

        self._usings.add("ResumableFunctions")
        
        funcdef = f"function {node.name}{node.template}({node.parsed_args}){node.return_type}"

        # Visit function body
        body = "\n".join(self.visit(n) for n in node.body)
        if body == "...":
            body = ""

        maybe_main = "\nmain()" if node.is_python_main else ""
        return f"@resumable {funcdef}\n{body}\nend\n{maybe_main}"


    def visit_offsetArrays(self, node, decorator):
        self._usings.add("OffsetArrays")


    # def visit_array(self, node, vargs):
    #     type_code: str = re.sub(r"\"", "", vargs[0])
    #     if type_code in TYPE_CODE_MAP:
    #         return f"Vector{{{TYPE_CODE_MAP[type_code]}}}"

    ######################################################################
    ########## Range ##########
    def visit_range(self, node, vargs: List[str]) -> str:
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

    ########## Builtin Functions ##########
    def visit_getattr(self, node, vargs: list[str]):
        parsed_args = JuliaTranspilerPlugins._parse_attrs(self, node)

        if len(parsed_args) == 3:
            # Cannot remove the quotes from default
            default = self.visit(node.args[-1])
            return f"""(hasfield(typeof({parsed_args[0]}), :{parsed_args[1]}) ? 
                getfield({parsed_args[0]}, :{parsed_args[1]}) : {default})"""
        elif len(parsed_args) == 2:
            return f"getfield({parsed_args[0]}, :{parsed_args[1]})"
        return "getfield"

    def visit_hasattr(self, node, vargs: list[str]):
        parsed_args = JuliaTranspilerPlugins._parse_attrs(self, node)
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

    def visit_argument_parser(self, node, vargs: list[str]):
        pass


    ########## Cast ##########
    def visit_cast_int(self, node, vargs) -> str:
        if hasattr(node, "args") and node.args:
            needs_parsing = False
            is_float = False
            for arg in node.args:
                if isinstance(arg, ast.Compare):
                    continue
                elif arg_type := self._typename_from_annotation(arg):
                    if arg_type.startswith("Float"):
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

    ########## String operations ##########
    def visit_maketrans(self, node, vargs: list[str]):
        original_lst = [vargs[0][i] for i in range(2, len(vargs[0]) - 1)]
        replacement_lst = []
        byte_replacements = str(vargs[1][2:-1])
        i = 0
        while i < len(byte_replacements):
            if byte_replacements[i:i+2] == "\\x":
                replacement_lst.append(str(byte_replacements[i:i+4]))
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

    def visit_join(self, node, vargs):
        if len(vargs) == 2:
            return f"join({vargs[1]}, {vargs[0]})"
        elif len(vargs) == 1:
            return f"x -> join(x, {vargs[0]})" 
        return "join"

    # TODO: Optimize (possibly using regex)
    def visit_format(self, node, vargs):
        subst_values: list[str] = vargs[1:]
        res: str = re.split("{|}", vargs[0])
        # Fill in empty curly braces
        cnt = 0
        for i in range(len(res)):
            r = res[i]
            if r == "":
                res[i] = f"{cnt}"
                cnt+=1
        # Create replacement map to replace original strings
        replacement_map = {}
        for i in range(len(subst_values)):
            subst_val = re.split("\s*=\s*", subst_values[i])
            if len(subst_val) > 1:
                original = subst_val[0]
                replacement = subst_val[1]
            else:
                original = f"{i}"
                replacement = subst_val[0]
            replacement_map[original] = replacement
        # Replace placeholders for values
        for j in range(1, len(res), 2):
            split_res = res[j].split(".")
            split_res[0] = split_res[0].translate(str.maketrans(replacement_map))
            res[j] = f"$({'.'.join(split_res)})"

        return "".join(res)

    def visit_translate(self,node, vargs):
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
                    arg = del_args[i:i+2]
                    i += 2
                else:
                    arg = del_args[i]
                    i += 1
                if arg in self._str_special_character_map:
                    arg = self._str_special_character_map[arg]
                key_map.append(f"b\"{arg}\" => b\"\"")
            key_map = ", ".join(key_map)
            translation_map = f"merge!({vargs[1]}, Dict({key_map}))"
        return f"replace!(collect({vargs[0]}), {translation_map}...)"

    ########## Array Operations ##########
    def visit_bytearray(self, node, vargs: list[str]):
        if len(vargs) == 0:
            return "Vector{UInt8}()"
        else:
            parsed_args = vargs[0]
            if isinstance(node.args[0], ast.GeneratorExp) \
                    or getattr(node.args[0], "is_gen_expr", None):
                parsed_args = parsed_args.removeprefix("(").removesuffix(")")
                parsed_args = f"[{vargs[0][1:-1]}]"
            return f"Vector{{UInt8}}({parsed_args})"

    def visit_islice(self, node, vargs: list[str]) -> str:
        node.is_gen_expr = True
        return f"({vargs[0]} for _ in (1:{vargs[1]}))"

    def visit_iter(self, node, vargs: list[str]) -> str:
        node.is_gen_expr = True
        return f"(x for x in {vargs[0]})"

    def visit_next(self, node: ast.Call, vargs: list[str]) -> str:
        func_def = get_func_def(node, vargs[0])
        if get_id(getattr(func_def, "annotation", None)) == "Generator":
            decs = getattr(func_def, "parsed_decorators", None)
            if RESUMABLE in decs:
                if len(vargs) > 1:
                    return f"{vargs[0]}({', '.split(vargs[1:])})"
                elif getattr(node, "is_attr", None):
                    return f"{vargs[0]}" 
                else :
                    return f"{vargs[0]}()"
            else:
                return f"take!({vargs[0]})"
        # TODO: Is this valid? Is this undecidable?
        # else:
        #     getattr(node, "is_gen_expr", None)
        #     return f"(({vargs[0]}, state) = iterate({vargs[0]}, state))"
        return f"next({', '.join(vargs)})"

    def visit_zip(self, node, vargs: list[str]):
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

    def visit_frozenset_contains(self, node, vargs):
        self._usings.add("FunctionalCollections")
        return f"{vargs[1]} in {vargs[0]}" \
            if len(vargs) == 2 else "x::pset, y -> y in x"

    ########## Bisect ##########
    def visit_bisect_right(self, node, vargs: list[str]):
        JuliaTranspilerPlugins._generic_bisect_visit(self)
        return f"bisect_right({', '.join(vargs)})" if vargs else "bisect_right"

    def visit_bisect_left(self, node, vargs: list[str]):
        JuliaTranspilerPlugins._generic_bisect_visit(self)
        return f"bisect_left({', '.join(vargs)})" if vargs else "bisect_left"

    def _generic_bisect_visit(self):
        self._usings.add("BisectPy")

    ########## IO ##########
    def visit_print(self, node: ast.Call, vargs: List[str]) -> str:
        if len(vargs) == 0:
            return "println()"
        if len(vargs) == 1 and not node.keywords and \
                not isinstance(node.args[0], ast.BinOp):
            return f"println({vargs[0]})"
        parsed_args = []
        args_str, args_vals = [], []
        for node_arg in node.args:
            arg = self.visit(node_arg)
            if arg.startswith("\""):
                arg = arg[1:-1]
            if isinstance(node_arg, ast.BinOp):
                if isinstance(node_arg.op, ast.Mod):
                    args_str.append(self.visit(node_arg.left)[1:-1])
                    args_vals.append(self.visit(node_arg.right))
                    parsed_args.append(arg)
                else:
                    parsed_bin_op = JuliaTranspilerPlugins._parse_bin_op(self, node_arg)
                    parsed_args.append(parsed_bin_op)
            elif isinstance(node_arg, ast.Constant):
                parsed_args.append(arg)
            elif isinstance(node_arg, ast.Call) and \
                    get_id(node_arg.func) == "format":
                parsed_args.append(arg)
            else:
                parsed_args.append(f"$({arg})")

        func_name = "println"
        sep = " "
        end = "\\n"
        flush = False
        print_repr = []
        for k in node.keywords:
            if k.arg == "file":
                func_name = "write"
                print_repr.append(self.visit(k.value))
            if k.arg == "end":
                val = ""
                if isinstance(k.value, ast.Constant):
                    val = k.value.value
                end = val
            if k.arg == "sep":
                sep = self.visit(k.value)
            if k.arg == "flush":
                flush = True

        if args_str and not print_repr:
            self._usings.add("Printf")
            return f'@printf(\"{sep.join(args_str)}{end}\", {", ".join(args_vals)})'

        # Append parsed arguments
        print_repr.append(f"\"{sep.join(parsed_args)}\"")

        maybe_flush = ""
        if flush:
            maybe_flush = f"\nflush({print_repr[0]})" \
                if func_name == "write" \
                else f"\nflush(stdout)"

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

    def visit_write(self, node, vargs: list[str]):
        func_name = JuliaTranspilerPlugins._handle_base_funcs(node, "write")

        if not vargs:
            # TODO: Is there a better way to name the variable?
            return f"x -> {func_name}(stdout, x)"
        return f"{func_name}(stdout, {vargs[0]})"

    def visit_flush(self, node, vargs: list[str]):
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

    def visit_textio_read(self, node, vargs):
        # TODO
        return None

    def visit_textio_write(self, node, vargs):
        # TODO
        return None

    def visit_encode(self, node, vargs):
        self._usings.add("StringEncodings")
        if len(vargs) == 0:
            return "encode"
        if len(vargs) == 1:
            return f"encode({self.visit(node.args[0])}, \"UTF-8\")"
        return f"encode({vargs[0]}, {vargs[1]})"

    def visit_ord(self, node, vargs):
        v0 = vargs[0].replace('\"', '\'')
        return f"Int(codepoint({v0}))"

    def visit_open(self, node, vargs):
        for_node = find_node_by_type(ast.For, node.scopes)
        # Check if this is always like this
        if for_node is not None:
            return f"readline({vargs[0]})"

        return f"open({vargs[0]}, {vargs[1]})"

    def visit_named_temp_file(self, node, vargs):
        node.annotation = ast.Name(id="tempfile._TemporaryFileWrapper")
        node.result_type = True
        return "NamedTempFile::new()"

    ########## regex ##########
    def visit_refindall(self, node, vargs):
        if len(vargs) == 1:
            return f"""
                # Unsupported use of re.findall with one arg
                findall({vargs[0]})"""
        else:
            vargs[0] = JuliaTranspilerPlugins._replace_regex_val(node.args[0],  
                vargs[0], "Regex", "r")
            if len(vargs) == 2:
                return f"collect(eachmatch({vargs[0]}, {vargs[1]}))"
            elif len(vargs) == 3:
                return f"""
                    # Flags unsupported
                    collect(eachmatch(r\"{vargs[0]}\", {vargs[1]}))"""

    def visit_resub(self, node, vargs):
        if len(vargs) < 3:
            return f"""
                # Unsupported use of re.sub with less than 3 arguments
                sub()"""
        else:
            vargs[0] = JuliaTranspilerPlugins._replace_regex_val(node.args[0],  
                vargs[0], "Regex", "r")
            vargs[1] = JuliaTranspilerPlugins._replace_regex_val(node.args[1], 
                vargs[1], "SubstitutionString", "s")
            return f"replace({vargs[2]}, {vargs[0]} => {vargs[1]})"

    def _replace_regex_val(arg, varg: str, val1, val2):
        if isinstance(arg, ast.Name):
            varg = f"{val1}({varg})"
        elif isinstance(arg, ast.Constant) and \
                isinstance(arg.value, str):
            varg = f"{val2}{varg}"
        return varg

    ########## importlib ##########
    def visit_import(self, node, vargs):
        # Try to split 'path' from 'name'
        path, name = os.path.split(vargs[0])
        return f"@eval @from {path} import Symbol({name})"

    ########## Path ##########
    def visit_makedirs(self, node: ast.Call, vargs):
        parsed_args = []
        # Ignore "exist_ok" parameter
        node_args = node.args if len(node.args) <= 2 else node.args[:2]
        for arg in node_args:
            parsed_args.append(self.visit(arg))
        accepted_keywords = set(["mode"])
        for keyword in node.keywords:
            if arg in accepted_keywords:
                parsed_args.append(self.visit(keyword))
        return f"mkpath({', '.join(parsed_args)})"

    ###### Random ######
    def visit_random(self, node: ast.Call, vargs: list[str]):
        self._usings.add("Random")
        return f"rand({', '.join(vargs)})"

    def visit_randomshuffle(self, node: ast.Call, vargs: list[str]):
        self._usings.add("Random")
        if vargs:
            return f"shuffle({', '.join(vargs)})"
        return "shuffle"

    def visit_randomseed(self, node: ast.Call, vargs: list[str]):
        self._usings.add("Random")
        return f"Random.seed!({','.join(vargs)})"

    ########## Async ##########
    @staticmethod
    def visit_asyncio_run(self, node, vargs) -> str:
        return f"block_on({vargs[0]})"

    ########## Special Assignments ##########
    def visit_all(self, node: ast.Assign, vargs):
        assert isinstance(node.value, ast.List)
        values = []
        for value in node.value.elts:
            values.append(value.value)
        return f"export {', '.join(values)}"


class SpecialFunctionsPlugins():
    def visit_init(self, node: ast.FunctionDef):
        # Remove self
        node.args.args = node.args.args[1:]
        arg_ids = set(map(lambda x: x.arg, node.args.args))
        is_oop = hasattr(node, "oop")
        constructor_calls = []
        constructor_body = []
        is_self = lambda x: isinstance(x, ast.Attribute) and \
            get_id(x.value) == "self"
        for n in node.body:
            if isinstance(n, ast.Assign) and is_self(n.targets[0]):
                new_id = get_id(n.targets[0]).split(".")[1:]
                ann = getattr(n.targets[0], "annotation", None)
                if new_id[0] not in arg_ids:
                    arg_node = ast.arg(arg = ".".join(new_id))
                    arg_node.annotation = ann
                    node.args.args.append(arg_node)
                    node.args.defaults.append(n.value)
            elif isinstance(n, ast.AnnAssign) and is_self(n.target):
                new_id = get_id(n.target).split(".")[1:]
                if new_id[0] not in arg_ids:
                    arg_node = ast.arg(arg = ".".join(new_id), annotation=n.annotation)
                    node.args.args.append(arg_node)
                    node.args.defaults.append(n.value)
            elif is_oop and isinstance(n, ast.Expr) and isinstance(n.value, ast.Call) \
                    and is_class_or_module(get_id(n.value.func), node.scopes):
                constructor_calls.append(n)
            else:
                constructor_body.append(n)

        # Class assignments
        class_node: ast.ClassDef = find_node_by_type(ast.ClassDef, node.scopes)
        for name, value in class_node.class_assignments.items():
            scopes = getattr(value, "scopes", None)
            if scopes and isinstance(scopes[-1], ast.ClassDef):
                arg_node = ast.arg(arg = name)
                if typename := self.visit(getattr(value, "annotation", None)):
                    arg_node.annotation = typename
                node.args.args.append(arg_node)
                node.args.defaults.append(value)
        
        constructor = None
        if is_oop:
            assignments = [ast.Assign(
                    targets = [ast.Name(id=arg)],
                    value = ast.Name(id=arg))
                for arg in class_node.declarations.keys()]
            body = constructor_calls + assignments
            make_block = juliaAst.Block(
                            name = "@mk",
                            body = body)
            ast.fix_missing_locations(make_block)
            constructor_body.append(make_block)
            constructor = ast.FunctionDef(
                name = "new",
                args = node.args,
                body = constructor_body,
            )
        else:
            struct_name = get_id(class_node)
            has_default = node.args.defaults != []
            if constructor_body or has_default:
                decls = list(map(lambda x: ast.Name(id=x.arg), node.args.args))
                new_instance = ast.Call(
                                func = ast.Name(id = "new"),
                                args = decls,
                                keywords = [],
                                scopes = ScopeList())
                ast.fix_missing_locations(new_instance)
                constructor_body.append(new_instance)
                constructor = juliaAst.Constructor(
                    name = struct_name,
                    args = node.args,
                    body = constructor_body,
                )

        if constructor:
            ast.fix_missing_locations(constructor)
            constructor.scopes = node.scopes,
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
        return f"""function Base.getproperty({node.parsed_args})
                {body}
            end"""

    def visit_show(self, node: ast.FunctionDef):
        docstring_parsed: str = self._get_docstring(node)
        body = [docstring_parsed] if docstring_parsed else []
        body.extend([self.visit(n) for n in node.body])
        body = "\n".join(body)
        return f"""function Base.show({node.parsed_args})
                {body}
            end"""


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
    "None": lambda n, vargs: f"Nothing",
    "sys.argv": lambda n, vargs: "append!([PROGRAM_FILE], ARGS)",
}

SMALL_USINGS_MAP = {"asyncio.run": "futures::executor::block_on"}

DISPATCH_MAP = {
    "xrange": JuliaTranspilerPlugins.visit_range,
    "print": JuliaTranspilerPlugins.visit_print,
    "int": JuliaTranspilerPlugins.visit_cast_int,
    "join": JuliaTranspilerPlugins.visit_join,
    "format": JuliaTranspilerPlugins.visit_format,
    "__next__": JuliaTranspilerPlugins.visit_next,
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
    "oop_class": JuliaTranspilerPlugins.visit_OOPClass,
    "resumable": JuliaTranspilerPlugins.visit_resumables,
    "offset_arrays": JuliaTranspilerPlugins.visit_offsetArrays
}

CLASS_DISPATCH_TABLE = {
    # "dataclass": JuliaTranspilerPlugins.visit_argparse_dataclass,
}

ATTR_DISPATCH_TABLE = {
    "temp_file.name": lambda self, node, value, attr: f"{value}.path()"
}

JULIA_SPECIAL_NAME_TABLE = {
    "__file__": "@__FILE__"
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
    frozenset.__contains__: (JuliaTranspilerPlugins.visit_frozenset_contains, False),
    tuple: (lambda self, node, vargs: f"tuple({vargs[0]}...)" 
        if isinstance(node.args[0], ast.GeneratorExp) else f"tuple({vargs[0]})", False),
    dict.items: (lambda self, node, vargs: f"collect({vargs[0]})", True),
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
    math.sqrt: (lambda self, node, vargs: f"sqrt({vargs[0]})", False),
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
    sys.stdin.read: (lambda self, node, vargs: f"read(stdin, String)" 
        if len(vargs) == 0 else f"read({vargs[0]}, {vargs[1]})", True),
    sys.stdin.write: (lambda self, node, vargs: f"open({vargs[0]})", True),
    sys.stdin.close: (lambda self, node, vargs: f"close({vargs[0]})", True),
    sys.exit: (lambda self, node, vargs: f"quit({vargs[0]})", True),
    sys.stdout: (lambda self, node, vargs: f"stdout", True),
    sys.stdout.buffer.write: (JuliaTranspilerPlugins.visit_write, True),
    sys.stdout.buffer.flush: (JuliaTranspilerPlugins.visit_flush, True),
    open: (JuliaTranspilerPlugins.visit_open, True),
    io.TextIOWrapper.read: (JuliaTranspilerPlugins.visit_textio_read, True),
    io.TextIOWrapper.write: (JuliaTranspilerPlugins.visit_textio_write, True),
    io.BytesIO: (lambda self, node, vargs: f"IOBuffer({vargs[0]})", True),
    os.unlink: (lambda self, node, vargs: f"std::fs::remove_file({vargs[0]})", True),
    NamedTemporaryFile: (JuliaTranspilerPlugins.visit_named_temp_file, True),
    pathlib.Path.cwd: (lambda self, node, vargs: "pwd()", True),
    # Instance checks
    isinstance: (lambda self, node, vargs: f"isa({vargs[0]}, {self._map_type(vargs[1])})", True),
    issubclass: (lambda self, node, vargs: f"{self._map_type(vargs[0])} <: {self._map_type(vargs[1])}", True),
    # Bisect
    bisect.bisect: (JuliaTranspilerPlugins.visit_bisect_right, True),
    bisect_right: (JuliaTranspilerPlugins.visit_bisect_right, True),
    bisect_left: (JuliaTranspilerPlugins.visit_bisect_left, True),
    # Random
    random.random: (JuliaTranspilerPlugins.visit_random, False),
    random.shuffle: (JuliaTranspilerPlugins.visit_randomshuffle, False),
    random.seed: (JuliaTranspilerPlugins.visit_randomseed,False,),
    # Str and Byte transformations
    str.join: (JuliaTranspilerPlugins.visit_join, False),
    str.format: (JuliaTranspilerPlugins.visit_format, False),  # Does not work
    bytes.maketrans: (JuliaTranspilerPlugins.visit_maketrans, True),
    bytearray.translate: (JuliaTranspilerPlugins.visit_translate, False),
    bytes.translate: (JuliaTranspilerPlugins.visit_translate, False),
    # Itertools
    itertools.repeat: (lambda self, node, vargs: f"repeat({vargs[0], vargs[1]})"
        if len(vargs) > 2 else f"repeat({vargs[0]})", False),
    itertools.islice: (JuliaTranspilerPlugins.visit_islice, True),
    # Time
    time.time: (lambda self, node, vargs: "pylib::time()", False),
    # Regex
    re.findall: (JuliaTranspilerPlugins.visit_refindall, False),
    re.sub: (JuliaTranspilerPlugins.visit_resub, False),
    # Memory handling
    contextlib.closing: (lambda self, node, vargs: vargs[0], False), #TODO: Is this correct
    # Traceback
    traceback.print_exc: (lambda self, node, vargs: "current_exceptions() != [] ? "\
        "current_exceptions()[end] : nothing", False),
    # builtin functions
    getattr: (JuliaTranspilerPlugins.visit_getattr , False),
    hasattr: (JuliaTranspilerPlugins.visit_hasattr , False),
    chr: (lambda self, node, vargs: f"Char({vargs[0]})", False),
    ord: (JuliaTranspilerPlugins.visit_ord, False),
    # Path
    os.path.split: (lambda self, node, vargs: f"splitdir({vargs[0]})", False),
    os.path.join: (lambda self, node, vargs: f"joinpath({', '.join(vargs)})", False),
    os.path.dirname: (lambda self, node, vargs: f"dirname({', '.join(vargs)})", False),
    os.makedirs: (JuliaTranspilerPlugins.visit_makedirs, False),
    os.remove: (lambda self, node, vargs: f"rm({vargs[0]})", False),
    os.unlink: (lambda self, node, vargs: f"rm({vargs[0]})", False),
    os.path.isdir: (lambda self, node, vargs: f"isdir({vargs[0]})", False),
    os.path.isfile: (lambda self, node, vargs: f"isfile({vargs[0]})", False),
    os.path.exists: (lambda self, node, vargs: f"ispath({vargs[0]})", False), # TODO: Is this too generic? 
    os.path.realpath: (lambda self, node, vargs: f"realpath({vargs[0]})", False),
    # os (generic)
    os.cpu_count: (lambda self, node, vargs: f"length(Sys.cpu_info())", True),
    # importlib
    importlib.import_module: (JuliaTranspilerPlugins.visit_import, False),
    importlib.__import__: (JuliaTranspilerPlugins.visit_import, False),
    importlib.invalidate_caches: (lambda self, node, vargs: "", True), # TODO: Nothing to support this
    # parsing args
    argparse.ArgumentParser: (JuliaTranspilerPlugins.visit_argument_parser, True),
    # sys special calls
    sys.exit: (lambda self, node, vargs: f"exit({vargs[0]})" if vargs else "exit()", True),
}


JULIA_SPECIAL_ASSIGNMENT_DISPATCH_TABLE = {
    "__all__": JuliaTranspilerPlugins.visit_all
}

JULIA_SPECIAL_FUNCTIONS = {
    "__getattr__": SpecialFunctionsPlugins.visit_getattr,
    "__repr__": SpecialFunctionsPlugins.visit_show
}