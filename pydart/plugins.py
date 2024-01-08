import functools
import sys
from typing import Callable, Dict, List, Tuple, Union


class DartTranspilerPlugins:
    def visit_range(self, node, vargs: List[str]) -> str:
        start = 0
        step = 1
        if len(vargs) == 1:
            end = vargs[0]
        elif len(node.args) == 2:
            start = vargs[0]
            end = vargs[1]
        elif len(node.args) == 3:
            start = vargs[0]
            end = vargs[1]
            step = vargs[2]
        else:
            raise Exception(
                "encountered range() call with unknown parameters: range({})".format(
                    vargs
                )
            )

        return f"([for(var i = {start}; i < {end}; i += {step}) i])"

    def visit_print(self, node, vargs: List[str]) -> str:
        placeholders = []
        for n in node.args:
            placeholders.append("%s")
        self._usings.add("package:sprintf/sprintf.dart")
        placeholders_str = " ".join(placeholders)
        vargs_str = ", ".join(vargs)
        return rf'print(sprintf("{placeholders_str}", [{vargs_str}]))'

    def visit_min_max(self, node, vargs, is_max: bool) -> str:
        min_max = "max" if is_max else "min"
        self._usings.add("dart:math")
        vargs_str = ", ".join(vargs)
        return f"{min_max}({vargs_str})"

    def visit_exit(self, node, vargs) -> str:
        self._usings.add("dart:io")
        return f"exit({vargs[0]})"


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs: f"{vargs[0]}.toString()" if vargs else '""',
    "len": lambda n, vargs: f"{vargs[0]}.length",
    "int": lambda n, vargs: f"{vargs[0]}.toInt()" if vargs else "0",
    "bool": lambda n, vargs: f"({vargs[0]} != 0)" if vargs else "false",
    "floor": lambda n, vargs: f"{vargs[0]}.floor()",
    "float": lambda n, vargs: f"{vargs[0]}.toDouble()" if vargs else "0",
}

SMALL_USINGS_MAP: Dict[str, str] = {}

DISPATCH_MAP = {
    "max": functools.partial(DartTranspilerPlugins.visit_min_max, is_max=True),
    "min": functools.partial(DartTranspilerPlugins.visit_min_max, is_max=False),
    "range": DartTranspilerPlugins.visit_range,
    "xrange": DartTranspilerPlugins.visit_range,
    "print": DartTranspilerPlugins.visit_print,
}

MODULE_DISPATCH_TABLE: Dict[str, str] = {}

DECORATOR_DISPATCH_TABLE = {}

CLASS_DISPATCH_TABLE = {}

ATTR_DISPATCH_TABLE = {
    "temp_file.name": lambda self, node, value, attr: f"{value}.path()",
}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    sys.exit: (DartTranspilerPlugins.visit_exit, True),
}
