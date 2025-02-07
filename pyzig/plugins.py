import functools
import random
import time
from typing import Callable, Dict, List, Tuple, Union


class ZigTranspilerPlugins:
    @staticmethod
    def visit_cast(node, vargs, cast_to: str) -> str:
        if not vargs:
            if cast_to == "Float64":
                return "0.0"
        return f"{cast_to}({vargs[0]})"

    def visit_print(self, node, vargs: List[str]) -> str:
        placeholders = []
        for n in node.args:
            placeholders.append("{}")
        self._aliases["print"] = "std.debug.print"
        return 'print("{}\\n", .{{{}}});'.format(
            " ".join(placeholders), ", ".join(vargs)
        )

    def visit_range(self, node, vargs: List[str]) -> str:
        if len(node.args) == 1:
            return f"(0..{vargs[0]})"
        elif len(node.args) == 2:
            return f"({vargs[0]}..{vargs[1]})"

        raise Exception(
            f"encountered range() call with unknown parameters: range({vargs})"
        )


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs: f"$({vargs[0]})" if vargs else '""',
    "bool": lambda n, vargs: f"bool({vargs[0]})" if vargs else "False",
    "int": lambda n, vargs: f"int({vargs[0]})" if vargs else "0",
    "floor": lambda n, vargs: f"int(floor({vargs[0]}))",
    "float": functools.partial(ZigTranspilerPlugins.visit_cast, cast_to="Float64"),
}

SMALL_USINGS_MAP: Dict[str, str] = {}

DISPATCH_MAP = {
    "print": ZigTranspilerPlugins.visit_print,
    "range": ZigTranspilerPlugins.visit_range,
}

MODULE_DISPATCH_TABLE: Dict[str, str] = {}

DECORATOR_DISPATCH_TABLE = {"dataclass": lambda n, vargs: "value"}

CLASS_DISPATCH_TABLE: Dict[type, Callable] = {}

ATTR_DISPATCH_TABLE: Dict[type, Callable] = {}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {}

FUNC_USINGS_MAP = {
    time.time: "pylib",
    random.seed: "pylib",
    random.random: "pylib",
}
