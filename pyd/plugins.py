import functools
import sys
from typing import Callable, Dict, List, Tuple, Union


class DTranspilerPlugins:
    def visit_range(self, node, vargs: List[str]) -> str:
        self._usings.add("std.range : iota")
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

        return f"iota({start}, {end}, {step})"

    def visit_print(self, node, vargs: List[str]) -> str:
        placeholders = []
        for n in node.args:
            placeholders.append("%s")
        self._usings.add("std")
        placeholders_str = " ".join(placeholders)
        vargs_str = ", ".join(vargs)
        return rf'writeln(format("{placeholders_str}", {vargs_str}))'

    def visit_min_max(self, node, vargs, is_max: bool) -> str:
        min_max = "max" if is_max else "min"
        vargs_str = ", ".join(vargs)
        return f"{min_max}({vargs_str})"

    def visit_exit(self, node, vargs) -> str:
        self._usings.add("core.stdc.stdlib:exit")
        return f"exit({vargs[0]})"


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs: f"{vargs[0]}.toString()" if vargs else '""',
    "len": lambda n, vargs: f"{vargs[0]}.length",
    "int": lambda n, vargs: f"{vargs[0]}.to!int" if vargs else "0",
    "bool": lambda n, vargs: f"({vargs[0]} != 0)" if vargs else "false",
    "floor": lambda n, vargs: f"{vargs[0]}.floor().to!long",  # long: int64
    "float": lambda n, vargs: f"{vargs[0]}.to!double" if vargs else "0",
}

SMALL_USINGS_MAP: Dict[str, str] = {}

DISPATCH_MAP = {
    "max": functools.partial(DTranspilerPlugins.visit_min_max, is_max=True),
    "min": functools.partial(DTranspilerPlugins.visit_min_max, is_max=False),
    "range": DTranspilerPlugins.visit_range,
    "xrange": DTranspilerPlugins.visit_range,
    "print": DTranspilerPlugins.visit_print,
}

MODULE_DISPATCH_TABLE: Dict[str, str] = {}

DECORATOR_DISPATCH_TABLE = {}

CLASS_DISPATCH_TABLE = {}

ATTR_DISPATCH_TABLE = {
    "temp_file.name": lambda self, node, value, attr: f"{value}.path()",
}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    sys.exit: (DTranspilerPlugins.visit_exit, True),
}
