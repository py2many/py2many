from dataclasses import dataclass
import io
import os
import ast
import sys
import textwrap

from tempfile import NamedTemporaryFile
from typing import Callable, Dict, List, Tuple, Union

from py2many.ast_helpers import get_id
from py2many.declaration_extractor import DeclarationExtractor
from pyjl.clike import KEYWORD_MAP
from pyjl.inference import JULIA_TYPE_MAP

try:
    from dataclasses import dataclass as ap_dataclass
    from dataclasses import ArgumentParser
except ImportError:
    ArgumentParser = "ArgumentParser"
    ap_dataclass = "ap_dataclass"


class JuliaTranspilerPlugins:
    def visit_argparse_dataclass(self, node, decorator):
        fields = []
        create_jl_annotation:bool = True
        for kw in decorator.keywords:
            arg = kw.arg
            value = kw.value
            if value == None:
                return None
            if arg == "create_jl_annotation":
                create_jl_annotation = value.value
            else:
                fields.append(f"_{arg}={KEYWORD_MAP[value.value]}")
        field = ""
        annotation = ""
        body = ""
        if create_jl_annotation:
            annotation = "@dataclass\n"
            field = "_initvars = [" + ", ".join(fields) + "]\n"
        else:
            body = self._generate_dataclass_methods(node, fields)       
        return annotation, field, body

    def _generate_dataclass_methods(self, node, annotation_fields) -> str:
        structname = get_id(node)

        # Get struct fields
        print(node)
        struct_fields = []
        for declaration, typename in declarations.items():
            struct_fields.append(declaration if typename == "" else f"{declaration}::{typename}")

        # get struct variables using getfield
        get_variables = []
        for field_name in struct_fields:
            get_variables.append(f"getfield!(self::{structname}, {field_name})")
        get_variables = ", ".join(get_variables)
        
        body = ""
        if annotation_fields["_init"]:
            str_struct_fields = ", ".join(struct_fields)
            assign_variables_init = ""
            for field_name in struct_fields:
                assign_variables_init += f"setfield!(self::{structname}, {field_name}, {field_name})\n"

            body += f"""
                function __init__(self::{structname}, {str_struct_fields})
                    {assign_variables_init}
                end\n
            """
        if annotation_fields["_repr"]:
            body += f"""
                function __repr__(self::{structname})::String
                    return {structname}({get_variables})
                end\n
            """
        if annotation_fields["_eq"]:
            body += f"""
                function __eq__(self::{structname}, other::{structname})::Bool
                    return __key(self) == __key(other)
                end\n
            """
        if annotation_fields["_order"]:
            body += f"""
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
        if annotation_fields["_unsafe_hash"]:
            if annotation_fields["_eq"]: # && ismutable
                body += f"""
                function __hash__(self::{structname})
                    return __key(self)
                end\n
                """

        body += f"""
                function __key(self::{structname})
                    ({get_variables})
                end\n
                """

        return body

    #################################################
    ################# TODO from here ################
    #################################################

    def visit_open(self, node, vargs):
        self._usings.add("std::fs::File")
        if len(vargs) > 1:
            self._usings.add("std::fs::OpenOptions")
            mode = vargs[1]
            opts = "OpenOptions::new()"
            is_binary = "b" in mode
            for c in mode:
                if c == "w":
                    if not is_binary:
                        self._usings.add("pylib::FileWriteString")
                    opts += ".write(true)"
                if c == "r":
                    if not is_binary:
                        self._usings.add("pylib::FileReadString")
                    opts += ".read(true)"
                if c == "a":
                    opts += ".append(true)"
                if c == "+":
                    opts += ".read(true).write(true)"
            node.result_type = True
            return f"{opts}.open({vargs[0]})"
        node.result_type = True
        return f"File::open({vargs[0]})"

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

    # def visit_ap_dataclass(self, cls):
    #     # Do whatever transformation the decorator does to cls here
    #     # print("ola")
    #     return cls

    def visit_range(self, node, vargs: List[str]) -> str:
        if len(node.args) == 1:
            return f"(0:{vargs[0]} - 1)"
        elif len(node.args) == 2:
            return f"({vargs[0]}:{vargs[1]} - 1)"
        elif len(node.args) == 3:
            return f"({vargs[0]}:{vargs[2]}:{vargs[1]}-1)"

        raise Exception(
            "encountered range() call with unknown parameters: range({})".format(vargs)
        )

    def visit_print(self, node, vargs: List[str]) -> str:
        args = ", ".join(vargs)
        # return f'println(join([{args}], " "))'
        return f"println({args})"

    def visit_cast_int(self, node, vargs) -> str:
        arg_type = self._typename_from_annotation(node.args[0])
        if arg_type is not None and arg_type.startswith("Float"):
            return f"Int64(floor({vargs[0]}))"
        return f"Int64({vargs[0]})"

    @staticmethod
    def visit_asyncio_run(node, vargs) -> str:
        return f"block_on({vargs[0]})"

JULIA_IMPORT_MAP = {
    "dataclass": "DataClass"
}

# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs: f"string({vargs[0]})",
    "len": lambda n, vargs: f"length({vargs[0]})",
    "enumerate": lambda n, vargs: f"{vargs[0]}.iter().enumerate()",
    "sum": lambda n, vargs: f"{vargs[0]}.iter().sum()",
    "bool": lambda n, vargs: f"Bool({vargs[0]})",
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

MODULE_DISPATCH_TABLE: Dict[str, str] = {}

# DECORATOR_DISPATCH_TABLE = {
#     ap_dataclass: JuliaTranspilerPlugins.visit_argparse_dataclass,
# }

DECORATOR_DISPATCH_TABLE = {
    "dataclass": JuliaTranspilerPlugins.visit_argparse_dataclass,
}

# CLASS_DISPATCH_TABLE = {
#     ap_dataclass: JuliaTranspilerPlugins.visit_argparse_dataclass,
# }

CLASS_DISPATCH_TABLE = {
    "dataclass": JuliaTranspilerPlugins.visit_argparse_dataclass,
}

ATTR_DISPATCH_TABLE = {
    "temp_file.name": lambda self, node, value, attr: f"{value}.path()",
}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    # Uncomment after upstream uploads a new version
    # ArgumentParser.parse_args: lambda node: "Opts::parse_args()",
    # HACKs: remove all string based dispatch here, once we replace them with type based
    "parse_args": (lambda self, node, vargs: "::from_args()", False),
    "f.read": (lambda self, node, vargs: "f.read_string()", True),
    "f.write": (lambda self, node, vargs: f"f.write_string({vargs[0]})", True),
    "f.close": (lambda self, node, vargs: "drop(f)", False),
    open: (JuliaTranspilerPlugins.visit_open, True),
    NamedTemporaryFile: (JuliaTranspilerPlugins.visit_named_temp_file, True),
    io.TextIOWrapper.read: (JuliaTranspilerPlugins.visit_textio_read, True),
    io.TextIOWrapper.read: (JuliaTranspilerPlugins.visit_textio_write, True),
    os.unlink: (lambda self, node, vargs: f"std::fs::remove_file({vargs[0]})", True),
    sys.exit: (lambda self, node, vargs: f"quit({vargs[0]})", True),
}
