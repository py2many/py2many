import io
import os
import ast
import functools
import textwrap

from tempfile import NamedTemporaryFile
from typing import Callable, Dict, List, Tuple, Union

try:
    from argparse_dataclass import dataclass as ap_dataclass
    from argparse_dataclass import ArgumentParser
except:
    ArgumentParser = "ArgumentParser"
    ap_dataclass = "ap_dataclass"


class CppTranspilerPlugins:
    def visit_argparse_dataclass(self, node):
        pass

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

    def visit_ap_dataclass(self, cls):
        # Do whatever transformation the decorator does to cls here
        return cls

    def visit_range(self, node, vargs: List[str]) -> str:
        if len(node.args) == 1:
            return "(0..{})".format(vargs[0])
        elif len(node.args) == 2:
            return "({}..{})".format(vargs[0], vargs[1])
        elif len(node.args) == 3:
            return "({}..{}).step_by({})".format(vargs[0], vargs[1], vargs[2])

        raise Exception(
            "encountered range() call with unknown parameters: range({})".format(vargs)
        )

    def visit_print(self, node, vargs: List[str]) -> str:
        placeholders = []
        for n in node.args:
            placeholders.append("{}")
        return 'println!("{0}",{1});'.format(" ".join(placeholders), ", ".join(vargs))

    def visit_min_max(self, node, vargs, is_max: bool) -> str:
        self._usings.add("std::cmp")
        min_max = "max" if is_max else "min"
        self._typename_from_annotation(node.args[0])
        if hasattr(node.args[0], "container_type"):
            node.result_type = True
            return f"{vargs[0]}.iter().{min_max}()"
        else:
            all_vargs = ", ".join(vargs)
            return f"cmp::{min_max}({all_vargs})"

    @staticmethod
    def visit_cast(node, vargs, cast_to: str) -> str:
        return f"{vargs[0]} as {cast_to}"

    @staticmethod
    def visit_asyncio_run(node, vargs) -> str:
        return f"block_on({vargs[0]})"


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs: f"&{vargs[0]}.to_string()",
    "len": lambda n, vargs: f"{vargs[0]}.len()",
    "enumerate": lambda n, vargs: f"{vargs[0]}.iter().enumerate()",
    "sum": lambda n, vargs: f"{vargs[0]}.iter().sum()",
    "int": functools.partial(CppTranspilerPlugins.visit_cast, cast_to="i32"),
    "bool": lambda n, vargs: f"({vargs[0]} != 0)",
    "float": functools.partial(CppTranspilerPlugins.visit_cast, cast_to="f64"),
    # as usize below is a hack to pass comb_sort.rs. Need a better solution
    "floor": lambda n, vargs: f"{vargs[0]}.floor() as usize",
    "reversed": lambda n, vargs: f"{vargs[0]}.iter().rev()",
    "map": lambda n, vargs: f"{vargs[1]}.iter().map({vargs[0]})",
    "filter": lambda n, vargs: f"{vargs[1]}.into_iter().filter({vargs[0]})",
    "list": lambda n, vargs: f"{vargs[0]}.collect::<Vec<_>>()",
    "asyncio.run": CppTranspilerPlugins.visit_asyncio_run,
}

SMALL_USINGS_MAP = {
    "asyncio.run": "futures::executor::block_on",
}

DISPATCH_MAP = {
    "max": functools.partial(CppTranspilerPlugins.visit_min_max, is_max=True),
    "min": functools.partial(CppTranspilerPlugins.visit_min_max, is_min=True),
    "range": CppTranspilerPlugins.visit_range,
    "xrange": CppTranspilerPlugins.visit_range,
    "print": CppTranspilerPlugins.visit_print,
}

MODULE_DISPATCH_TABLE = {}

DECORATOR_DISPATCH_TABLE = {ap_dataclass: CppTranspilerPlugins.visit_ap_dataclass}

CLASS_DISPATCH_TABLE = {ap_dataclass: CppTranspilerPlugins.visit_argparse_dataclass}

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
    open: (CppTranspilerPlugins.visit_open, True),
    NamedTemporaryFile: (CppTranspilerPlugins.visit_named_temp_file, True),
    io.TextIOWrapper.read: (CppTranspilerPlugins.visit_textio_read, True),
    io.TextIOWrapper.read: (CppTranspilerPlugins.visit_textio_write, True),
    os.unlink: (lambda self, node, vargs: f"std::fs::remove_file({vargs[0]})", True),
}
