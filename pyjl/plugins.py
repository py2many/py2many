import argparse
import io
import itertools
import math
import time
import os
import ast
import random
import re
import sys

from tempfile import NamedTemporaryFile
from typing import Any, Callable, Dict, List, Optional, Set, Tuple, Union

from py2many.ast_helpers import get_id
from ctypes import c_int8, c_int16, c_int32, c_int64
from ctypes import c_uint8, c_uint16, c_uint32, c_uint64

from py2many.tracer import find_node_matching_type

try:
    from dataclasses import dataclass
except ImportError:
    ArgumentParser = "ArgumentParser"
    ap_dataclass = "ap_dataclass"


class JuliaTranspilerPlugins:
    def visit_jl_dataclass(t_self, node: ast.ClassDef, decorator):
        t_self._usings.add("DataClass")

        dataclass_data = JuliaTranspilerPlugins._generic_dataclass_visit(
            decorator)
        d_fields, field_repr = dataclass_data[0], dataclass_data[1]

        # Visit class fields
        fields = "\n".join([
            node.fields,
            "_initvars = [" + ", ".join(field_repr) + "]\n"
        ])

        # Struct definition
        bases = [t_self.visit(base) for base in node.bases]
        struct_def = f"mutable struct {node.name} <: {bases[0]}" \
            if bases else f"mutable struct {node.name}"

        body = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                body.append(t_self.visit(b))
        body = "\n".join(body)
        return f"""
            @dataclass {struct_def} begin
                {fields}
            end
            {body}
        """

    def visit_py_dataclass(t_self, node: ast.ClassDef, decorator) -> str:
        dataclass_data = JuliaTranspilerPlugins._generic_dataclass_visit(
            decorator)
        [d_fields, _] = dataclass_data[0], dataclass_data[1]

        fields: str = node.fields
        struct_fields = fields.split("\n")

        # Abstract type
        struct_name = "".join(["Abstract", get_id(node)])

        # get struct variables using getfield
        attr_vars = []
        key_vars = []
        assign_variables_init = []
        str_struct_fields = []
        for field in struct_fields:
            field_name, field_type = field.split("::")
            st_name = field_type
            if field_type.startswith("Abstract"):
                st_name = field_type[8:]
            attr_vars.append(f"self.{field_name}")
            key_vars.append(f"self.{field_name}"
                            if (st_name not in t_self._class_names) else f"__key(self.{field_name})")
            assign_variables_init.append(
                f"setfield!(self::{struct_name}, :{field_name}, {field})")
            str_struct_fields.append(f"{field_name}::{field_type}"
                                     if field_type not in t_self._class_names
                                     else f"{field_name}::Abstract{field_type}")        

        # Convert into string
        key_vars = ", ".join(key_vars)
        attr_vars = ", ".join(attr_vars)
        assign_variables_init = ", ".join(assign_variables_init)
        str_struct_fields = ", ".join(str_struct_fields)

        # Visit class body
        body = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                body.append(t_self.visit(b))

        # Add functions to body
        if d_fields["init"]:
            body.append(f"""
                function __init__(self::{struct_name}, {str_struct_fields})
                    {assign_variables_init}
                end
            """)
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

        bases = [t_self.visit(base) for base in node.bases]
        struct_def = f"mutable struct {node.name} <: {bases[0]}" \
            if bases else f"mutable struct {node.name}"

        if hasattr(node, "constructors"):
            return f"{struct_def}\n{fields}\n{node.constructors}\nend\n{body}"
        
        return f"{struct_def}\n{fields}\nend\n{body}"
        

    def _generic_dataclass_visit(decorator):
        fields = {}
        field_repr = []
        keywords = {'init': True, 'repr': True, 'eq': True, 'order': False,
                    'unsafe_hash': False, 'frozen': False}

        # Parse received keywords if needed
        if isinstance(decorator, ast.Call):
            received_keywords = decorator.keywords
            for x in received_keywords:
                if x.arg in keywords:
                    keywords[x.arg] = x.value.value

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
        # Struct definition
        bases = []
        for b in node.bases:
            b_name = t_self.visit(b)
            if b_name != f"Abstract{node.name}":
                bases.append(b_name)
        struct_def = f"{node.name} <: {', '.join(bases)}" \
            if bases else f"{node.name}"

        body = []
        for b in node.body:
            if isinstance(b, ast.FunctionDef):
                body.append(f"{t_self.visit(b)}")
        body = "\n".join(body)

        if hasattr(node, "constructor"):
            return f"@class {struct_def}begin\n{node.fields}\n{node.constructors}\nend\n{body}"

        return f"@class {struct_def} begin\n{node.fields}\nend\n{body}"

    def visit_async_ann(self, node, decorator):
        return ""

    #################################################
    ################# TODO from here ################
    #################################################

    def visit_open(self, node, vargs):
        for_node = find_node_matching_type(ast.For, node.scopes)
        # Check if this is always like this
        if for_node is not None:
            return f"readline({vargs[0]})"

        return f"open({vargs[0]}, {vargs[1]})"

    def visit_named_temp_file(self, node, vargs):
        node.annotation = ast.Name(id="tempfile._TemporaryFileWrapper")
        node.result_type = True
        return "NamedTempFile::new()"

    def visit_textio_read(self, node, vargs):
        # TODO
        return None

    def visit_textio_write(self, node, vargs):
        # TODO
        return None

    def visit_ap_dataclass(self, cls):
        # Do whatever transformation the decorator does to cls here
        return cls

    def visit_range(self, node, vargs: List[str]) -> str:
        end = vargs[0] if len(vargs) == 1 else vargs[1]
        if ((isinstance(end, str) and end.lstrip("-").isnumeric())
                or isinstance(end, int) or isinstance(end, float)):
            end = int(end) - 1
        else:
            end += " - 1"

        if len(node.args) == 1:
            return f"(0:{end})"
        elif len(node.args) == 2:
            return f"({vargs[0]}:{end})"
        elif len(node.args) == 3:
            return f"({vargs[0]}:{vargs[2]}:{end})"

        raise Exception(
            "encountered range() call with unknown parameters: range({})".format(vargs)
        )

    def visit_print(self, node, vargs: List[str]) -> str:
        args = ", ".join(vargs)
        if "%" in args:
            # TODO: Further rules are necessary
            res = re.split(r"\s\%\s", args)
            args = ", ".join(res)
            self._usings.add("Printf")
            return f"@printf({args})"
        return f"println({args})"

    def visit_cast_int(self, node, vargs) -> str:
        if hasattr(node, "args") and node.args:
            arg_type = self._typename_from_annotation(node.args[0])
            if arg_type is not None and arg_type.startswith("Float"):
                return f"Int64(floor({vargs[0]}))"
        if vargs:
            return f"parse(Int64, {vargs[0]})"
        return f"zero(Int)"  # Default int value

    @staticmethod
    def visit_asyncio_run(node, vargs) -> str:
        return f"block_on({vargs[0]})"


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

# JULIA_IGNORED_FUNCTIONS = [
#     "__init__",
#     "__str__",
# ]

CONTAINER_DISPATCH_TABLE = {
    List: "Vector",
    Dict: "Dict",
    Set: "Set",
    Optional: "nothing",
    bytearray: f"Vector{{Int8}}"
}

# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda node, vargs: f"string({vargs[0]})" if vargs else f"string()",
    "len": lambda n, vargs: f"length({vargs[0]})",
    "enumerate": lambda n, vargs: f"{vargs[0]}.iter().enumerate()",
    # default is false
    "bool": lambda n, vargs: f"Bool({vargs[0]})" if vargs else f"false",
    # ::Int64 below is a hack to pass comb_sort.jl. Need a better solution
    "floor": lambda n, vargs: f"Int64(floor({vargs[0]}))",
    "None": lambda n, vargs: f"nothing",
}

SMALL_USINGS_MAP = {
    "asyncio.run": "futures::executor::block_on",
}

DISPATCH_MAP = {
    "range": JuliaTranspilerPlugins.visit_range,
    "xrange": JuliaTranspilerPlugins.visit_range,
    "print": JuliaTranspilerPlugins.visit_print,
    "int": JuliaTranspilerPlugins.visit_cast_int,
}

MODULE_DISPATCH_TABLE: Dict[str, str] = {
    "dataclass": "DataClass",
    "json": "JSON",
    "datetime": "Dates",
    "bisect": "BisectPy"
}

DECORATOR_DISPATCH_TABLE = {
    "jl_dataclass": JuliaTranspilerPlugins.visit_jl_dataclass,
    "dataclass": JuliaTranspilerPlugins.visit_py_dataclass,
    "jl_class": JuliaTranspilerPlugins.visit_JuliaClass
}

CLASS_DISPATCH_TABLE = {
    "bytearray": (lambda self, node, vargs: f"Vector{{Int8}}()", True),
    # "dataclass": JuliaTranspilerPlugins.visit_argparse_dataclass,
}

ATTR_DISPATCH_TABLE = {
    "temp_file.name": lambda self, node, value, attr: f"{value}.path()",
}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    # Array Support
    list.append: (lambda self, node, vargs: f"push!({vargs[0]}, {vargs[1]})", True),
    list.clear: (lambda self, node, vargs: f"empty!({vargs[0]})", True),
    list.remove: (lambda self, node, vargs: \
                  f"{vargs[0]} = deleteat!({vargs[0]}, findfirst(isequal({vargs[1]}), {vargs[0]}))", True),
    list.extend: (lambda self, node, vargs: f"{vargs[0]} = append!({vargs[0]}, {vargs[1]})", True),
    list.count: (lambda self, node, vargs: f"count(isequal({vargs[1]}), {vargs[0]})", True),
    list.index: (lambda self, node, vargs: f"findfirst(isequal({vargs[1]}), {vargs[0]})", True),
    list: (lambda self, node, vargs: f"Vector()" if len(vargs) == 0 else f"collect({vargs[0]})", True),
    bytearray: (lambda self, node, vargs: f"Vector{{UInt8}}()" \
                if len(vargs) == 0 \
                else f"Vector{{UInt8}}(join({vargs[0]}, \"\"))", True),
    itertools.islice: (lambda self, node, vargs: f"split({vargs[0]})[{vargs[1]}]", True),
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
    sum: (lambda self, node, vargs: f"sum({', '.join(vargs)})", False),
    round: (lambda self, node, vargs: f"round({vargs[0]}, digits = {vargs[1]})", False),
    # io
    argparse.ArgumentParser.parse_args: (lambda self, node, vargs: "::from_args()", False),
    sys.stdin.read: (lambda self, node, vargs: f"open({vargs[0]}, r)", True),
    sys.stdin.write: (lambda self, node, vargs: f"open({vargs[0]})", True),
    sys.stdin.close: (lambda self, node, vargs: f"close({vargs[0]})", True),
    open: (JuliaTranspilerPlugins.visit_open, True),
    io.TextIOWrapper.read: (JuliaTranspilerPlugins.visit_textio_read, True),
    io.TextIOWrapper.read: (JuliaTranspilerPlugins.visit_textio_write, True),
    os.unlink: (lambda self, node, vargs: f"std::fs::remove_file({vargs[0]})", True),
    # sys
    sys.exit: (lambda self, node, vargs: f"quit({vargs[0]})", True),
    sys.stdout.buffer.write: (lambda self, node, vargs: f"write(IOStream, {vargs[0]})", True),
    # misc
    str.format: (lambda self, node, vargs: f"test", True),  # Does not work
    isinstance: (lambda self, node, vargs: f"isa({vargs[0]}, {vargs[1]})", True),
    NamedTemporaryFile: (JuliaTranspilerPlugins.visit_named_temp_file, True),
    time.time: (lambda self, node, vargs: "pylib::time()", False),
    random.seed: (
        lambda self, node, vargs: f"pylib::random::reseed_from_f64({vargs[0]})",
        False,
    ),
    random.random: (lambda self, node, vargs: "pylib::random::random()", False),
    # TODO: remove string-based fallback
    # os.cpu_count: (lambda self, node, vargs: f"length(Sys.cpu_info())", True),
    "cpu_count": (lambda self, node, vargs: f"length(Sys.cpu_info())", True),
}
