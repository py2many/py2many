import functools
import random
import sys
import time
from typing import Callable, Dict, List, Tuple, Union


class NimTranspilerPlugins:
    def visit_range(self, node, vargs: List[str]) -> str:
        if len(node.args) == 1:
            return f"(0..{vargs[0]} - 1)"
        elif len(node.args) == 2:
            return f"({vargs[0]}..{vargs[1]} - 1)"
        elif len(node.args) == 3:
            return f"countup({vargs[0]}, {vargs[1]} - 1, {vargs[2]})"

        raise Exception(
            f"encountered range() call with unknown parameters: range({vargs})"
        )

    @staticmethod
    def visit_cast(node, vargs, cast_to: str) -> str:
        if not vargs:
            if cast_to == "float":
                return "0.0"
        return f"{cast_to}({vargs[0]})"

    def visit_print(self, node, vargs: List[str]) -> str:
        args = []
        for n in vargs:
            args.append(n)
            args.append('" "')
        args = ", ".join(args[:-1])
        return f"echo {args}"


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs: f"$({vargs[0]})" if vargs else '""',
    "bool": lambda n, vargs: f"bool({vargs[0]})" if vargs else "false",
    "int": lambda n, vargs: f"int({vargs[0]})" if vargs else "0",
    "floor": lambda n, vargs: f"int(floor({vargs[0]}))",
    "float": functools.partial(NimTranspilerPlugins.visit_cast, cast_to="float"),
}

SMALL_USINGS_MAP: Dict[str, str] = {}

DISPATCH_MAP = {
    "range": NimTranspilerPlugins.visit_range,
    "xrange": NimTranspilerPlugins.visit_range,
    "print": NimTranspilerPlugins.visit_print,
}

MODULE_DISPATCH_TABLE: Dict[str, str] = {}

DECORATOR_DISPATCH_TABLE = {}

CLASS_DISPATCH_TABLE: Dict[type, Callable] = {}

ATTR_DISPATCH_TABLE: Dict[type, Callable] = {}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    sys.exit: (lambda self, node, vargs: f"quit({vargs[0]})", True),
}

FUNC_USINGS_MAP = {
    time.time: "pylib",
    random.seed: "pylib",
    random.random: "pylib",
}
