import io
import os
import functools

from tempfile import NamedTemporaryFile
from typing import Callable, Dict, List, Tuple, Union

try:
    from argparse_dataclass import dataclass as ap_dataclass
    from argparse_dataclass import ArgumentParser
except:
    ArgumentParser = "ArgumentParser"
    ap_dataclass = "ap_dataclass"


class NimTranspilerPlugins:
    def visit_open(self, node, vargs):
        # TODO
        return None

    def visit_named_temp_file(self, node, vargs):
        # TODO
        return None

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
    "int": functools.partial(NimTranspilerPlugins.visit_cast, cast_to="i32"),
    "bool": lambda n, vargs: f"({vargs[0]} != 0)",
    "float": functools.partial(NimTranspilerPlugins.visit_cast, cast_to="f64"),
    # as usize below is a hack to pass comb_sort.rs. Need a better solution
    "floor": lambda n, vargs: f"{vargs[0]}.floor() as usize",
    "reversed": lambda n, vargs: f"{vargs[0]}.iter().rev()",
    "map": lambda n, vargs: f"{vargs[1]}.iter().map({vargs[0]})",
    "filter": lambda n, vargs: f"{vargs[1]}.into_iter().filter({vargs[0]})",
    "list": lambda n, vargs: f"{vargs[0]}.collect::<Vec<_>>()",
    "asyncio.run": NimTranspilerPlugins.visit_asyncio_run,
}

SMALL_USINGS_MAP = {
    "asyncio.run": "futures::executor::block_on",
}

DISPATCH_MAP = {
    "max": functools.partial(NimTranspilerPlugins.visit_min_max, is_max=True),
    "min": functools.partial(NimTranspilerPlugins.visit_min_max, is_min=True),
    "range": NimTranspilerPlugins.visit_range,
    "xrange": NimTranspilerPlugins.visit_range,
    "print": NimTranspilerPlugins.visit_print,
}

MODULE_DISPATCH_TABLE = {}

DECORATOR_DISPATCH_TABLE = {ap_dataclass: NimTranspilerPlugins.visit_ap_dataclass}

CLASS_DISPATCH_TABLE = {}

ATTR_DISPATCH_TABLE = {}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    open: (NimTranspilerPlugins.visit_open, True),
    NamedTemporaryFile: (NimTranspilerPlugins.visit_named_temp_file, True),
    io.TextIOWrapper.read: (NimTranspilerPlugins.visit_textio_read, True),
    io.TextIOWrapper.read: (NimTranspilerPlugins.visit_textio_write, True),
    os.unlink: (lambda self, node, vargs: f"std::fs::remove_file({vargs[0]})", True),
}
