import functools
import re
import sys
from typing import Callable, Dict, List, Tuple, Union


class KotlinTranspilerPlugins:
    def visit_range(self, node, vargs: List[str]) -> str:
        if len(node.args) == 1:
            return f"(0..{vargs[0]}-1)"
        elif len(node.args) == 2:
            return f"({vargs[0]}..{vargs[1]}-1)"
        elif len(node.args) == 3:
            return f"({vargs[0]}..{vargs[1]}-1 step {vargs[2]})"

        raise Exception(
            f"encountered range() call with unknown parameters: range({vargs})"
        )

    def visit_print(self, node, vargs: List[str]) -> str:
        def _format(arg):
            if arg.isdigit():
                return arg
            if re.match(r"'.*'", arg) or re.match(r'".*"', arg):
                return arg[1:-1]
            else:
                return f"${arg}"

        vargs_str = " ".join([f"{_format(arg)}" for arg in vargs])
        return f'println("{vargs_str}")'

    def visit_min_max(self, node, vargs, is_max: bool) -> str:
        min_max = "max" if is_max else "min"
        self._usings.add(f"kotlin.math.{min_max}")
        self._typename_from_annotation(node.args[0])
        if hasattr(node.args[0], "container_type"):
            return f"maxOf({vargs[0]})"
        else:
            all_vargs = ", ".join(vargs)
            return f"{min_max}({all_vargs})"

    @staticmethod
    def visit_cast(node, vargs, cast_to: str) -> str:
        if not vargs:
            if cast_to == "Double":
                return "0.0"
        return f"{vargs[0]}.to{cast_to}()"

    def visit_floor(self, node, vargs) -> str:
        self._usings.add("kotlin.math.floor")
        return f"floor({vargs[0]}).toInt()"


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs: f"{vargs[0]}.toString()" if vargs else '""',
    # TODO: strings use .length
    "len": lambda n, vargs: f"{vargs[0]}.size",
    "int": lambda n, vargs: f"{vargs[0]}.toInt()" if vargs else "0",
    "float": functools.partial(KotlinTranspilerPlugins.visit_cast, cast_to="Double"),
    "bool": lambda n, vargs: f"({vargs[0]} != 0)" if vargs else "false",
    "reversed": lambda n, vargs: f"{vargs[0]}.reversed()",
}

SMALL_USINGS_MAP: Dict[str, str] = {}

DISPATCH_MAP = {
    "max": functools.partial(KotlinTranspilerPlugins.visit_min_max, is_max=True),
    "min": functools.partial(KotlinTranspilerPlugins.visit_min_max, is_max=False),
    "range": KotlinTranspilerPlugins.visit_range,
    "xrange": KotlinTranspilerPlugins.visit_range,
    "print": KotlinTranspilerPlugins.visit_print,
    "floor": KotlinTranspilerPlugins.visit_floor,
}

MODULE_DISPATCH_TABLE: Dict[str, str] = {}

DECORATOR_DISPATCH_TABLE = {}

CLASS_DISPATCH_TABLE = {}

ATTR_DISPATCH_TABLE = {}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    sys.exit: (
        lambda self, node, vargs: f"kotlin.system.exitProcess({vargs[0]})",
        True,
    ),
}
