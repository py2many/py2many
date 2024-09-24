import functools
import sys
from typing import Callable, Dict, List, Tuple, Union


class GoTranspilerPlugins:
    def visit_range(self, node, vargs: List[str]) -> str:
        self._usings.add('iter "github.com/hgfischer/go-iter"')
        if len(node.args) == 1:
            return f"iter.NewIntSeq(iter.Start(0), iter.Stop({vargs[0]})).All()"
        elif len(node.args) == 2:
            return (
                f"iter.NewIntSeq(iter.Start({vargs[0]}), iter.Stop({vargs[1]})).All()"
            )
        elif len(node.args) == 3:
            return f"iter.NewIntSeq(iter.Start({vargs[0]}), iter.Stop({vargs[1]}), iter.Step({vargs[2]})).All()"

        raise Exception(
            f"encountered range() call with unknown parameters: range({vargs})"
        )

    def visit_print(self, node, vargs: List[str]) -> str:
        placeholders = []
        for n in node.args:
            placeholders.append("%v")
        self._usings.add('"fmt"')
        placeholders_str = " ".join(placeholders)
        vargs_str = ", ".join(vargs)
        return f'fmt.Printf("{placeholders_str}\\n",{vargs_str})'

    def visit_min_max(self, node, vargs, is_max: bool) -> str:
        min_max = "math.Max" if is_max else "math.Min"
        self._usings.add('"math"')
        vargs_str = ", ".join(vargs)
        return f"{min_max}({vargs_str})"

    @staticmethod
    def visit_cast(node, vargs, cast_to: str) -> str:
        if not vargs:
            if cast_to == "float64":
                return "0.0"
        return f"{cast_to}({vargs[0]})"

    def visit_floor(self, node, vargs) -> str:
        self._usings.add('"math"')
        return f"math.Floor({vargs[0]})"

    def visit_exit(self, node, vargs) -> str:
        self._usings.add('"os"')
        return f"os.Exit({vargs[0]})"


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs: f"String({vargs[0]})" if vargs else '""',
    "int": lambda n, vargs: f"int({vargs[0]})" if vargs else "0",
    "bool": lambda n, vargs: f"({vargs[0]} != 0)" if vargs else "false",
    "float": functools.partial(GoTranspilerPlugins.visit_cast, cast_to="float64"),
}

SMALL_USINGS_MAP: Dict[str, str] = {}

DISPATCH_MAP = {
    "max": functools.partial(GoTranspilerPlugins.visit_min_max, is_max=True),
    "min": functools.partial(GoTranspilerPlugins.visit_min_max, is_max=False),
    "range": GoTranspilerPlugins.visit_range,
    "range_": GoTranspilerPlugins.visit_range,
    "xrange": GoTranspilerPlugins.visit_range,
    "print": GoTranspilerPlugins.visit_print,
    "floor": GoTranspilerPlugins.visit_floor,
}

MODULE_DISPATCH_TABLE: Dict[str, str] = {}

DECORATOR_DISPATCH_TABLE = {}

CLASS_DISPATCH_TABLE = {}

ATTR_DISPATCH_TABLE = {}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    sys.exit: (GoTranspilerPlugins.visit_exit, True),
}
