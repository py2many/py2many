import argparse
import io
import itertools
from msilib.schema import File
import os
import ast
import re
import sys 
# from sys import stdout

from tempfile import NamedTemporaryFile
from typing import Callable, Dict, List, Tuple, Union

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
    def visit_jl_dataclass(transpiler_mod, node, decorator):
        transpiler_mod._usings.add("DataClass")

        dataclass_data = JuliaTranspilerPlugins._generic_dataclass_visit(decorator)
        fields, field_repr = dataclass_data[0], dataclass_data[1]

        fields_str, annotation, body, modifiers = "", "", "", ""
        # if it defines init it needs to be mutable
        if fields["init"]:
            modifiers = "mutable"
        annotation = "@dataclass "
        fields_str = "_initvars = [" + ", ".join(field_repr) + "]\n"
        return annotation, fields_str, modifiers, body 


    def visit_py_dataclass(transpiler_mod, node, decorator) -> str:
        dataclass_data = JuliaTranspilerPlugins._generic_dataclass_visit(decorator)
        [fields, _] = dataclass_data[0], dataclass_data[1]

        fields_str, annotation, body, modifiers = "", "", "", ""

        structname = get_id(node)

        # Get struct fields
        struct_fields = []
        for declaration in node.declarations:
            (struct_fields.append(declaration if node.declarations[declaration] == "" 
                else f"{declaration}::{node.declarations[declaration]}"))

        
        # get struct variables using getfield
        get_variables = []
        for field_name in struct_fields:
            get_variables.append(f"getfield!(self::{structname}, {field_name})")
        get_variables = ", ".join(get_variables)

        if fields["init"]:
            modifiers = "mutable"
            str_struct_fields = ", ".join(struct_fields)
            assign_variables_init = ""
            for field in struct_fields:
                field_name = field.split("::")
                assign_variables_init += f"setfield!(self::{structname}, :{field_name[0]}, {field})\n"

            body += f"""
                function __init__(self::{structname}, {str_struct_fields})
                    {assign_variables_init}
                end\n
            """
        if fields["repr"]:
            body += f"""function __repr__(self::{structname})::String
                return {structname}({get_variables})
            end\n"""
        if fields["eq"]:
            body += f"""\
                function __eq__(self::{structname}, other::{structname})::Bool
                    return __key(self) == __key(other)
                end\n
            """
        if fields["order"]:
            body += f"""\
                function __lt__(self::{structname}, other::{structname})::Bool
                    return __key(self) < __key(other)
                end\n
                function __le__(self::{structname}, other::{structname})::Bool
                    return __key(self) <= __key(other)
                end\n
                function __gt__(self::{structname}, other::{structname})::Bool
                    return __key(self) > __key(other)
                end\n
                function __ge__(self::{structname}, other::{structname})::Bool
                    return __key(self) >= __key(other)
                end\n
            """
        if fields["unsafe_hash"]:
            if fields["_eq"]: # && ismutable
                body += f"""\
                function __hash__(self::{structname})
                    return __key(self)
                end\n
                """

        body += f"""\
                function __key(self::{structname})
                    ({get_variables})
                end\n
                """

        return annotation, fields_str, modifiers, body 

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
                return None
            fields[arg] = value
            field_repr.append(f"_{arg}={key_map[value]}")

        return fields, field_repr



    ############ 
    # Continuables support
    def visit_continuables_ann(self, node, decorator):
        annotation, body = "", ""
        self._usings.add("Continuables")
        annotation = "@cont "
        return annotation, body


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
                or isinstance(end, int) or  isinstance(end, float)):
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
        return f"zero(Int)" # Default int value

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
}

VARIABLE_MAP = {
    "c_int8": c_int8,
    "c_int16": c_int16,
    "c_int32": c_int32,
    "c_int64": c_int64,
    "c_uint8": c_uint8,
    "c_uint16": c_uint16,
    "c_uint32": c_uint32,
    "c_uint64": c_uint64,
}

INTEGER_TYPES = (
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
)

NUM_TYPES = INTEGER_TYPES + ["Float64"]

CONTAINER_TYPE_MAP = {
    "Array": "Array",
    "List": "Vector",
    "Dict": "Dict",
    "Set": "Set",
    "Optional": "Nothing",
    "bytearray": f"Vector{{Int8}}"
}


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda node, vargs: f"string({vargs[0]})" if vargs else f"string()",
    "len": lambda n, vargs: f"length({vargs[0]})",
    "enumerate": lambda n, vargs: f"{vargs[0]}.iter().enumerate()",
    "sum": lambda n, vargs: f"{vargs[0]}.iter().sum()",
    "bool": lambda n, vargs: f"Bool({vargs[0]})" if vargs else f"false", # default is false
    # ::Int64 below is a hack to pass comb_sort.jl. Need a better solution
    "floor": lambda n, vargs: f"Int64(floor({vargs[0]}))",
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
    "use_continuables": JuliaTranspilerPlugins.visit_continuables_ann
}

CLASS_DISPATCH_TABLE = {
    "bytearray": (lambda self, node, vargs: f"Vector{{Int8}}()", True),
    # "dataclass": JuliaTranspilerPlugins.visit_argparse_dataclass,
}

ATTR_DISPATCH_TABLE = {
    "temp_file.name": lambda self, node, value, attr: f"{value}.path()",
}

FuncType = Union[Callable, str]


# Functions have string-based fallback
FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    # Uncomment after upstream uploads a new version
    # ArgumentParser.parse_args: lambda node: "Opts::parse_args()",
    # HACKs: remove all string based dispatch here, once we replace them with type based
    argparse.ArgumentParser.parse_args: (lambda self, node, vargs: "::from_args()", False),
    "f.read": (lambda self, node, vargs: "f.read_string()", True),
    "f.write": (lambda self, node, vargs: f"f.write_string({vargs[0]})", True),
    "f.close": (lambda self, node, vargs: "drop(f)", False),
    open: (JuliaTranspilerPlugins.visit_open, True),
    # Array Support
    list.append: (lambda self, node, vargs: f"push!({vargs[0]}, {vargs[1]})", True),
    list.clear: (lambda self, node, vargs: f"empty!({vargs[0]})", True),
    list.remove: (lambda self, node, vargs: f"{vargs[0]} = deleteat!({vargs[0]}, findfirst(isequal({vargs[1]}), {vargs[0]}))", True),
    list.extend: (lambda self, node, vargs: f"{vargs[0]} = append!({vargs[0]}, {vargs[1]})", True),
    list.count: (lambda self, node, vargs: f"count(isequal({vargs[1]}), {vargs[0]})", True),
    list.index: (lambda self, node, vargs: f"findfirst(isequal({vargs[1]}), {vargs[0]})", True),
    # 
    isinstance: (lambda self, node, vargs: f"isa({vargs[0]}, {vargs[1]})", True),
    NamedTemporaryFile: (JuliaTranspilerPlugins.visit_named_temp_file, True),
    io.TextIOWrapper.read: (JuliaTranspilerPlugins.visit_textio_read, True),
    io.TextIOWrapper.read: (JuliaTranspilerPlugins.visit_textio_write, True),
    os.unlink: (lambda self, node, vargs: f"std::fs::remove_file({vargs[0]})", True),
    sys.exit: (lambda self, node, vargs: f"quit({vargs[0]})", True),
    list: (lambda self, node, vargs: f"Vector()" if len(vargs) == 0 else f"collect({vargs[0]})", True),
    bytearray: (lambda self, node, vargs: f"Vector{{UInt8}}()" if len(vargs) == 0 else f"Vector{{UInt8}}(join({vargs[0]}, \"\"))", True),
    itertools.islice: (lambda self, node, vargs: f"split({vargs[0]})[{vargs[1]}]", True),
    sys.stdout.buffer.write: (lambda self, node, vargs: f"write(IOStream, {vargs[0]})", True),
    # os.cpu_count: (lambda self, node, vargs: f"length(Sys.cpu_info())", True), # For later
    "cpu_count": (lambda self, node, vargs: f"length(Sys.cpu_info())", True),
    str.format: (lambda self, node, vargs: f"test", True), # Does not work
}