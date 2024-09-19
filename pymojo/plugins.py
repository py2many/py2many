import functools
import random
import time
from typing import Callable, Dict, List, Tuple, Union


class MojoTranspilerPlugins:
    @staticmethod
    def visit_cast(node, vargs, cast_to: str) -> str:
        if not vargs:
            if cast_to == "Float64":
                return "0.0"
        return f"{cast_to}({vargs[0]})"

    def visit_print(self, node, vargs: List[str]) -> str:
        args = ", ".join(vargs)
        return f"print({args})"


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs: f"$({vargs[0]})" if vargs else '""',
    "bool": lambda n, vargs: f"bool({vargs[0]})" if vargs else "False",
    "int": lambda n, vargs: f"int({vargs[0]})" if vargs else "0",
    "floor": lambda n, vargs: f"int(floor({vargs[0]}))",
    "float": functools.partial(MojoTranspilerPlugins.visit_cast, cast_to="Float64"),
}

SMALL_USINGS_MAP: Dict[str, str] = {}

DISPATCH_MAP = {
    "print": MojoTranspilerPlugins.visit_print,
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
