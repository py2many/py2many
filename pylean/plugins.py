import ast
import functools
from typing import Callable, Dict, List, Tuple, Union


def _is_string_arg(arg_node) -> bool:
    """Check if an AST argument node is a string literal."""
    return isinstance(arg_node, ast.Constant) and isinstance(arg_node.value, str)


class LeanTranspilerPlugins:
    @staticmethod
    def visit_cast(node, vargs, cast_to: str) -> str:
        if not vargs:
            if cast_to == "Float":
                return "0.0"
            return f"(0 : {cast_to})"
        if cast_to == "Int":
            return f"(Int.ofNat {vargs[0]})"
        if cast_to == "Float":
            return f"(Float.ofNat {vargs[0]})"
        return f"({vargs[0]} : {cast_to})"

    def visit_print(self, node, vargs: List[str]) -> str:
        # Python's print joins its arguments with spaces and appends a newline;
        # IO.println adds the newline, so join the (stringified) args ourselves.
        if not vargs:
            return 'IO.println ""'
        if len(vargs) == 1:
            arg = vargs[0]
            # Strings don't need toString; everything else does.
            if _is_string_arg(node.args[0]):
                return f"IO.println {arg}"
            return f"IO.println (toString {arg})"
        parts = []
        for i, a in enumerate(vargs):
            if _is_string_arg(node.args[i]):
                parts.append(a)
            else:
                parts.append(f"toString {a}")
        joined = ", ".join(parts)
        return f'IO.println (String.intercalate " " [{joined}])'

    def visit_range(self, node, vargs: List[str]) -> str:
        if len(node.args) == 1:
            return f"(List.range {vargs[0]})"
        elif len(node.args) == 2:
            return f"(List.range' {vargs[0]} ({vargs[1]} - {vargs[0]}))"
        elif len(node.args) == 3:
            return f"(List.range' {vargs[0]} (({vargs[1]} - {vargs[0]}) / {vargs[2]}) {vargs[2]})"

        raise Exception(
            f"encountered range() call with unknown parameters: range({vargs})"
        )

    def visit_len(self, node, vargs: List[str]) -> str:
        return f"({vargs[0]}).length"

    def visit_sys_exit(self, node, vargs: List[str]) -> str:
        # IO.Process.exit takes a UInt8; the integer literal coerces to it.
        code = vargs[0] if vargs else "0"
        return f"IO.Process.exit {code}"

    def visit_max(self, node, vargs: List[str]) -> str:
        if len(vargs) == 2:
            return f"(Nat.max {vargs[0]} {vargs[1]})"
        return f"(Nat.max {' '.join(vargs)})"

    def visit_min(self, node, vargs: List[str]) -> str:
        if len(vargs) == 2:
            return f"(Nat.min {vargs[0]} {vargs[1]})"
        return f"(Nat.min {' '.join(vargs)})"

    def visit_floor(self, node, vargs: List[str]) -> str:
        return f"(Float.toUInt64 (Float.floor {vargs[0]})).toNat"

    def visit_append(self, node, vargs: List[str], attr: str, value_id: str) -> str:
        return f"{value_id} := {value_id} ++ [{vargs[0]}]"


def _visit_list_append(transpiler, node, value_id, attr):
    """Handle list.append(val) -> list := list ++ [val]"""
    # This is called from the ATTR_DISPATCH_TABLE; the actual call
    # arguments are on the parent Call node, not available here.
    # We return a marker that visit_Call will recognise.
    return f"{value_id}.append"


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs: f"(toString {vargs[0]})" if vargs else '""',
    "bool": lambda n, vargs: f"({vargs[0]} != 0)" if vargs else "false",
    "int": functools.partial(LeanTranspilerPlugins.visit_cast, cast_to="Int"),
    "float": functools.partial(LeanTranspilerPlugins.visit_cast, cast_to="Float"),
    "abs": lambda n, vargs: f"(Int.natAbs {vargs[0]})",
    "not": lambda n, vargs: f"(!{vargs[0]})",
}

SMALL_USINGS_MAP: Dict[str, str] = {}

DISPATCH_MAP = {
    "print": LeanTranspilerPlugins.visit_print,
    "range": LeanTranspilerPlugins.visit_range,
    "len": LeanTranspilerPlugins.visit_len,
    "sys.exit": LeanTranspilerPlugins.visit_sys_exit,
    "max": LeanTranspilerPlugins.visit_max,
    "min": LeanTranspilerPlugins.visit_min,
    "floor": LeanTranspilerPlugins.visit_floor,
    "math.floor": LeanTranspilerPlugins.visit_floor,
}

MODULE_DISPATCH_TABLE: Dict[str, str] = {}

DECORATOR_DISPATCH_TABLE: Dict[str, Callable] = {}

ATTR_DISPATCH_TABLE: Dict[type, Callable] = {}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {}

FUNC_USINGS_MAP: Dict[Callable, str] = {}
