import functools
from typing import Callable, Dict, List, Tuple, Union


class LeanTranspilerPlugins:
    @staticmethod
    def visit_cast(node, vargs, cast_to: str) -> str:
        if not vargs:
            if cast_to == "Float":
                return "0.0"
            return f"(0 : {cast_to})"
        return f"({vargs[0]} : {cast_to})"

    def visit_print(self, node, vargs: List[str]) -> str:
        # Python's print joins its arguments with spaces and appends a newline;
        # IO.println adds the newline, so join the (stringified) args ourselves.
        if not vargs:
            return 'IO.println ""'
        if len(vargs) == 1:
            return f"IO.println {vargs[0]}"
        joined = ", ".join(f"toString {a}" for a in vargs)
        return f'IO.println (String.intercalate " " [{joined}])'

    def visit_range(self, node, vargs: List[str]) -> str:
        if len(node.args) == 1:
            return f"(List.range {vargs[0]})"
        elif len(node.args) == 2:
            return f"(List.range' {vargs[0]} ({vargs[1]} - {vargs[0]}))"

        raise Exception(
            f"encountered range() call with unknown parameters: range({vargs})"
        )

    def visit_len(self, node, vargs: List[str]) -> str:
        return f"({vargs[0]}).length"

    def visit_sys_exit(self, node, vargs: List[str]) -> str:
        # IO.Process.exit takes a UInt8; the integer literal coerces to it.
        code = vargs[0] if vargs else "0"
        return f"IO.Process.exit {code}"


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs: f"(toString {vargs[0]})" if vargs else '""',
    "bool": lambda n, vargs: f"({vargs[0]} != 0)" if vargs else "false",
    "int": lambda n, vargs: f"(Int.ofNat {vargs[0]})" if vargs else "0",
    "float": functools.partial(LeanTranspilerPlugins.visit_cast, cast_to="Float"),
    "abs": lambda n, vargs: f"({vargs[0]}).natAbs",
}

SMALL_USINGS_MAP: Dict[str, str] = {}

DISPATCH_MAP = {
    "print": LeanTranspilerPlugins.visit_print,
    "range": LeanTranspilerPlugins.visit_range,
    "len": LeanTranspilerPlugins.visit_len,
    "sys.exit": LeanTranspilerPlugins.visit_sys_exit,
}

MODULE_DISPATCH_TABLE: Dict[str, str] = {}

DECORATOR_DISPATCH_TABLE: Dict[str, Callable] = {}

ATTR_DISPATCH_TABLE: Dict[type, Callable] = {}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {}

FUNC_USINGS_MAP: Dict[Callable, str] = {}
