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
        printed_args = []
        for n in node.args:
            placeholders.append("%v")
            printed_args.append(self._print_value(n))
        self._usings.add('"fmt"')
        placeholders_str = " ".join(placeholders)
        vargs_str = ", ".join(printed_args)
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

    def visit_ord(self, node, vargs) -> str:
        # ord() over a 1-character string. Go strings iterate as runes,
        # but py2many renders `for ch in s` loops as 1-byte strings, so
        # decode through []rune to get the code point.
        return f"int([]rune({vargs[0]})[0])"

    def visit_chr(self, node, vargs) -> str:
        return f"string(rune({vargs[0]}))"

    def visit_exit(self, node, vargs) -> str:
        self._usings.add('"os"')
        return f"os.Exit({vargs[0]})"


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs: f'fmt.Sprintf("%v", {vargs[0]})' if vargs else '""',
    "int": lambda n, vargs: f"int({vargs[0]})" if vargs else "0",
    "bool": lambda n, vargs: f"({vargs[0]} != 0)" if vargs else "false",
    "float": functools.partial(GoTranspilerPlugins.visit_cast, cast_to="float64"),
    "complex": functools.partial(GoTranspilerPlugins.visit_cast, cast_to="complex128"),
}

SMALL_USINGS_MAP: Dict[str, str] = {
    "str": '"fmt"',
}

DISPATCH_MAP = {
    "max": functools.partial(GoTranspilerPlugins.visit_min_max, is_max=True),
    "min": functools.partial(GoTranspilerPlugins.visit_min_max, is_max=False),
    "range": GoTranspilerPlugins.visit_range,
    "range_": GoTranspilerPlugins.visit_range,
    "xrange": GoTranspilerPlugins.visit_range,
    "print": GoTranspilerPlugins.visit_print,
    "floor": GoTranspilerPlugins.visit_floor,
    "ord": GoTranspilerPlugins.visit_ord,
    "chr": GoTranspilerPlugins.visit_chr,
}

MODULE_DISPATCH_TABLE: Dict[str, str] = {}

DECORATOR_DISPATCH_TABLE = {}

CLASS_DISPATCH_TABLE = {}

ATTR_DISPATCH_TABLE = {}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    sys.exit: (GoTranspilerPlugins.visit_exit, True),
}
