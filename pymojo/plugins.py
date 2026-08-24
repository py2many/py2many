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

    @staticmethod
    def visit_sys_exit(transpiler, node, value_id: str, attr: str) -> str:
        # mojo 1.0: exit lives in std.sys; import it as a bare name
        transpiler._from_imports.add(("std.sys", "exit"))
        return "exit"


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs: f"$({vargs[0]})" if vargs else '""',
    "bool": lambda n, vargs: f"bool({vargs[0]})" if vargs else "False",
    "int": lambda n, vargs: f"Int({vargs[0]})" if vargs else "0",
    "floor": lambda n, vargs: f"Int(floor(Float64({vargs[0]})))",
    "float": functools.partial(MojoTranspilerPlugins.visit_cast, cast_to="Float64"),
}

SMALL_USINGS_MAP: Dict[str, str] = {}

DISPATCH_MAP = {
    "print": MojoTranspilerPlugins.visit_print,
}

MODULE_DISPATCH_TABLE: Dict[str, str] = {}

DECORATOR_DISPATCH_TABLE = {"dataclass": lambda n, vargs: ""}

CLASS_DISPATCH_TABLE: Dict[type, Callable] = {}

ATTR_DISPATCH_TABLE = {"sys.exit": MojoTranspilerPlugins.visit_sys_exit}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {}

FUNC_USINGS_MAP = {
    time.time: "pylib",
    random.seed: "pylib",
    random.random: "pylib",
}
