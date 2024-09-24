import ast
import functools
import io
import math
import os
import random
import sys
from typing import Callable, Dict, List, Tuple, Union

from py2many.analysis import get_id


class CppTranspilerPlugins:
    def _translate_file(file: str) -> str:
        FILE_MAP: Dict[object, str] = {
            "sys.stdout": "std::cout",
            "sys.stdin": "std::cin",
            "sys.stderr": "std::cerr",
        }
        return FILE_MAP.get(file, file)

    def visit_textio_read(self, node, vargs):
        # TODO
        return None

    def visit_textio_write(self, node, vargs):
        self._usings.add("<iostream>")
        return f"{CppTranspilerPlugins._translate_file(get_id(node.func.value))} << {vargs[0]}"

    def visit_textio_flush(self, node, vargs):
        self._usings.add("<iostream>")
        return (
            f"{CppTranspilerPlugins._translate_file(get_id(node.func.value))}.flush()"
        )

    def visit_range(self, node, vargs: List[str]) -> str:
        self._usings.add("<cppitertools/range.hpp>")
        args = ", ".join(vargs)
        return f"iter::range({args})"

    def visit_print(self, node, vargs: List[str]) -> str:
        self._usings.add("<iostream>")
        buf = []
        for n in node.args:
            value = self.visit(n)
            if isinstance(n, ast.List) or isinstance(n, ast.Tuple):
                buf.append(
                    "std::cout << {};".format(
                        " << ".join([self.visit(el) for el in n.elts])
                    )
                )
            else:
                buf.append(f"std::cout << {value};")
            buf.append('std::cout << " ";')
        buf.pop()
        return "\n".join(buf) + "\nstd::cout << std::endl;"

    def visit_min_max(self, node, vargs, is_max: bool) -> str:
        min_max = "max" if is_max else "min"
        if hasattr(node.args[0], "container_type"):
            self._usings.add("<algorithm>")
            return f"*std::{min_max}_element({vargs[0]}.begin(), {vargs[0]}.end());"
        else:
            # C++ can't deal with max(1, size_t), but size_t support here has been
            # removed as size_t support here causes other problems
            all_vargs = ", ".join(vargs)
            return f"std::{min_max}({all_vargs})"

    def visit_random(self, node, vargs) -> str:
        self._usings.add("<cstdlib>")
        return "(static_cast<float>(rand()) / static_cast<float>(RAND_MAX))"

    @staticmethod
    def visit_cast(node, vargs, cast_to: str) -> str:
        return f"static_cast<{cast_to}>({vargs[0]})"

    @staticmethod
    def visit_floor(node, vargs) -> str:
        return f"static_cast<int>(floor({vargs[0]}))"


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "int": functools.partial(CppTranspilerPlugins.visit_cast, cast_to="int"),
    "chr": functools.partial(CppTranspilerPlugins.visit_cast, cast_to="char"),
    "str": lambda n, vargs: f"std::to_string({vargs[0]})" if vargs else '""',
    "bool": lambda n, vargs: f"static_cast<bool>({vargs[0]})" if vargs else "false",
    "len": lambda n, vargs: f"static_cast<int>({vargs[0]}.size())",
    "float": functools.partial(CppTranspilerPlugins.visit_cast, cast_to="float"),
    "floor": CppTranspilerPlugins.visit_floor,
}

SMALL_USINGS_MAP = {
    "floor": "<math.h>",
}

DISPATCH_MAP = {
    "max": functools.partial(CppTranspilerPlugins.visit_min_max, is_max=True),
    "min": functools.partial(CppTranspilerPlugins.visit_min_max, is_max=False),
    "range": CppTranspilerPlugins.visit_range,
    "xrange": CppTranspilerPlugins.visit_range,
    "print": CppTranspilerPlugins.visit_print,
}

MODULE_DISPATCH_TABLE = {
    "time": "<chrono>",
    "random": "<cstdlib>",
}

DECORATOR_DISPATCH_TABLE = {}

CLASS_DISPATCH_TABLE = {}


def emit_argv(self, node, value, attr):
    self._usings.add("<string>")
    self._usings.add("<vector>")
    return "std::vector<std::string>(argv, argv + argc)"


ATTR_DISPATCH_TABLE = {
    "sys.argv": emit_argv,
}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    io.TextIOWrapper.read: (CppTranspilerPlugins.visit_textio_read, True),
    io.TextIOWrapper.write: (CppTranspilerPlugins.visit_textio_write, True),
    io.TextIOWrapper.flush: (CppTranspilerPlugins.visit_textio_flush, True),
    math.asin: (lambda self, node, vargs: f"std::asin({vargs[0]})", False),
    math.acos: (lambda self, node, vargs: f"std::acos({vargs[0]})", False),
    math.cos: (lambda self, node, vargs: f"std::cos({vargs[0]})", False),
    math.atan: (lambda self, node, vargs: f"std::atan({vargs[0]})", False),
    math.pow: (lambda self, node, vargs: f"std::pow({vargs[0]}, {vargs[1]})", False),
    random.random: (CppTranspilerPlugins.visit_random, False),
    random.seed: (
        lambda self, node, vargs: f"srand(static_cast<int>({vargs[0]}))",
        False,
    ),
    os.unlink: (lambda self, node, vargs: f"std::fs::remove_file({vargs[0]})", True),
    sys.exit: (lambda self, node, vargs: f"exit({vargs[0]})", True),
}
