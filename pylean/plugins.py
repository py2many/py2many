import ast
import functools
import io
import sys
from typing import Callable, Dict, List, Tuple, Union

from py2many.analysis import get_id


def _get_annotation_id(node) -> str:
    """Return the annotation id string for an AST node, or empty string."""
    ann = getattr(node, "annotation", None)
    if ann:
        aid = get_id(ann)
        if aid:
            return aid
    return ""


def _is_bool_arg(arg_node) -> bool:
    """Check if an AST argument node is a boolean literal or variable typed Bool."""
    if isinstance(arg_node, ast.Constant) and isinstance(arg_node.value, bool):
        return True
    ann_id = _get_annotation_id(arg_node)
    return ann_id == "bool"


def _is_string_arg(arg_node) -> bool:
    """Check if an AST argument node is a string literal."""
    return isinstance(arg_node, ast.Constant) and isinstance(arg_node.value, str)


def _is_float_arg(arg_node) -> bool:
    """Check if an AST argument node is a float literal or variable typed Float."""
    if isinstance(arg_node, ast.Constant) and isinstance(arg_node.value, float):
        return True
    ann_id = _get_annotation_id(arg_node)
    return ann_id == "float"


class LeanTranspilerPlugins:
    @staticmethod
    def visit_cast(node, vargs, cast_to: str) -> str:
        if not vargs:
            if cast_to == "Float":
                return "0.0"
            if cast_to == "Nat":
                return "0"
            return f"(0 : {cast_to})"
        if cast_to == "Nat":
            # int() in Python: convert float to int, or identity on int
            if node.args and _is_float_arg(node.args[0]):
                return f"({vargs[0]}).toUInt64.toNat"
            return f"({vargs[0]} : Nat)"
        if cast_to == "Float":
            if node.args and _is_float_arg(node.args[0]):
                return vargs[0]
            return f"(Float.ofNat {vargs[0]})"
        return f"({vargs[0]} : {cast_to})"

    def visit_print(self, node, vargs: List[str]) -> str:
        # Python's print joins its arguments with spaces and appends a newline;
        # IO.println adds the newline, so join the (stringified) args ourselves.
        if not vargs:
            return 'IO.println ""'

        def _stringify(i, a):
            if _is_string_arg(node.args[i]):
                return a
            if _is_bool_arg(node.args[i]):
                return f'(if {a} then "True" else "False")'
            if _is_float_arg(node.args[i]):
                self._needs_float_to_string = True
                return f"floatToString {a}"
            return f"toString {a}"

        if len(vargs) == 1:
            arg = vargs[0]
            if _is_string_arg(node.args[0]):
                return f"IO.println {arg}"
            if _is_bool_arg(node.args[0]):
                return f'IO.println (if {arg} then "True" else "False")'
            if _is_float_arg(node.args[0]):
                self._needs_float_to_string = True
                return f"IO.println (floatToString {arg})"
            return f"IO.println (toString {arg})"
        parts = [_stringify(i, a) for i, a in enumerate(vargs)]
        joined = ", ".join(parts)
        return f'IO.println (String.intercalate " " [{joined}])'

    def visit_range(self, node, vargs: List[str]) -> str:
        # Python's range produces ints; Lean's List.range produces Nat.
        # We keep Nat since most Lean APIs (List indexing, etc.) expect Nat.
        if len(node.args) == 1:
            return f"(List.range {vargs[0]})"
        elif len(node.args) == 2:
            start, stop = vargs
            return f"(List.range' {start} ({stop} - {start}))"
        elif len(node.args) == 3:
            start, stop, step = vargs
            return f"(List.range' {start} (({stop} - {start}) / {step}) {step})"

        raise Exception(
            f"encountered range() call with unknown parameters: range({vargs})"
        )

    def visit_len(self, node, vargs: List[str]) -> str:
        # Std.HashMap uses .size; List/String/Array use .length
        if node.args:
            arg = node.args[0]
            # Check annotation
            ann = getattr(arg, "annotation", None)
            if ann:
                ann_id = get_id(ann)
                if ann_id:
                    ann_str = str(ann_id)
                    if "Dict" in ann_str or "HashMap" in ann_str or "dict" in ann_str:
                        return f"({vargs[0]}).size"
                if isinstance(ann, ast.Subscript):
                    val_id = get_id(ann.value) if hasattr(ann, "value") else ""
                    if val_id and ("Dict" in val_id or "dict" in val_id):
                        return f"({vargs[0]}).size"
            # Check container_type
            ct = getattr(arg, "container_type", None)
            if ct:
                ct_str = str(ct)
                if "Dict" in ct_str or "dict" in ct_str or "HashMap" in ct_str:
                    return f"({vargs[0]}).size"
            # Check if variable was assigned from a DictComp or Dict literal
            if isinstance(arg, ast.Name):
                name = get_id(arg)
                if hasattr(self, "_dict_vars") and name in self._dict_vars:
                    return f"({vargs[0]}).size"
                if hasattr(arg, "scopes"):
                    defn = arg.scopes.find(name)
                    if defn and hasattr(defn, "value"):
                        if isinstance(defn.value, (ast.Dict, ast.DictComp)):
                            return f"({vargs[0]}).size"
        return f"({vargs[0]}).length"

    def visit_sys_exit(self, node, vargs: List[str]) -> str:
        # IO.Process.exit takes a UInt8; the integer literal coerces to it.
        code = vargs[0] if vargs else "0"
        return f"IO.Process.exit {code}"

    def visit_max(self, node, vargs: List[str]) -> str:
        return f"(max {' '.join(vargs)})"

    def visit_min(self, node, vargs: List[str]) -> str:
        return f"(min {' '.join(vargs)})"

    def visit_floor(self, node, vargs: List[str]) -> str:
        return f"(Float.toUInt64 (Float.floor {vargs[0]})).toNat"

    def visit_append(self, node, vargs: List[str], attr: str, value_id: str) -> str:
        return f"{value_id} := {value_id} ++ [{vargs[0]}]"

    def visit_textio_write(self, node, vargs: List[str]) -> str:
        """Handle sys.stdout.write(text) -> IO.print text"""
        return f"IO.print {vargs[0]}"

    def visit_textio_flush(self, node, vargs: List[str]) -> str:
        return "(pure () : IO Unit)"

    def visit_sorted(self, node, vargs: List[str]) -> str:
        return f"(List.mergeSort {vargs[0]})"

    def visit_reversed(self, node, vargs: List[str]) -> str:
        return f"({vargs[0]}).reverse"

    def visit_enumerate(self, node, vargs: List[str]) -> str:
        return f"({vargs[0]}).enum"

    def visit_sum(self, node, vargs: List[str]) -> str:
        return f"({vargs[0]}).foldl (· + ·) 0"

    def visit_map(self, node, vargs: List[str]) -> str:
        if len(vargs) == 2:
            return f"(({vargs[1]}).map {vargs[0]})"
        return f"(List.map {vargs[0]})"

    def visit_filter(self, node, vargs: List[str]) -> str:
        if len(vargs) == 2:
            return f"(({vargs[1]}).filter {vargs[0]})"
        return f"(List.filter {vargs[0]})"

    def visit_list(self, node, vargs: List[str]) -> str:
        if vargs:
            return vargs[0]
        return "([] : List _)"

    @staticmethod
    def visit_math_sqrt(self, node, vargs: List[str]) -> str:
        return f"(Float.sqrt {vargs[0]})"

    @staticmethod
    def visit_math_pow(self, node, vargs: List[str]) -> str:
        return f"({vargs[0]} ^ {vargs[1]})"

    @staticmethod
    def visit_math_sin(self, node, vargs: List[str]) -> str:
        return f"(Float.sin {vargs[0]})"

    @staticmethod
    def visit_math_cos(self, node, vargs: List[str]) -> str:
        return f"(Float.cos {vargs[0]})"

    @staticmethod
    def visit_math_tan(self, node, vargs: List[str]) -> str:
        return f"(Float.tan {vargs[0]})"

    @staticmethod
    def visit_math_log(self, node, vargs: List[str]) -> str:
        return f"(Float.log {vargs[0]})"

    @staticmethod
    def visit_math_log2(self, node, vargs: List[str]) -> str:
        return f"(Float.log2 {vargs[0]})"

    @staticmethod
    def visit_math_ceil(self, node, vargs: List[str]) -> str:
        return f"(Float.ceil {vargs[0]})"


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
    "int": functools.partial(LeanTranspilerPlugins.visit_cast, cast_to="Nat"),
    "float": functools.partial(LeanTranspilerPlugins.visit_cast, cast_to="Float"),
    "abs": lambda n, vargs: f"(Int.natAbs {vargs[0]})",
    "not": lambda n, vargs: f"(!{vargs[0]})",
    "sorted": lambda n, vargs: f"(List.mergeSort {vargs[0]})",
    "reversed": lambda n, vargs: f"({vargs[0]}).reverse",
    "enumerate": lambda n, vargs: f"({vargs[0]}).enum",
    "sum": lambda n, vargs: f"({vargs[0]}).foldl (· + ·) 0",
    "map": lambda n, vargs: (
        f"(({vargs[1]}).map {vargs[0]})"
        if len(vargs) == 2
        else f"(List.map {vargs[0]})"
    ),
    "filter": lambda n, vargs: (
        f"(({vargs[1]}).filter {vargs[0]})"
        if len(vargs) == 2
        else f"(List.filter {vargs[0]})"
    ),
    "list": lambda n, vargs: vargs[0] if vargs else "([] : List _)",
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
    "math.sqrt": LeanTranspilerPlugins.visit_math_sqrt,
    "math.pow": LeanTranspilerPlugins.visit_math_pow,
    "math.sin": LeanTranspilerPlugins.visit_math_sin,
    "math.cos": LeanTranspilerPlugins.visit_math_cos,
    "math.tan": LeanTranspilerPlugins.visit_math_tan,
    "math.log": LeanTranspilerPlugins.visit_math_log,
    "math.log2": LeanTranspilerPlugins.visit_math_log2,
    "math.ceil": LeanTranspilerPlugins.visit_math_ceil,
}

MODULE_DISPATCH_TABLE: Dict[str, str] = {}

DECORATOR_DISPATCH_TABLE: Dict[str, Callable] = {}

ATTR_DISPATCH_TABLE: Dict[type, Callable] = {}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    io.TextIOWrapper.write: (LeanTranspilerPlugins.visit_textio_write, True),
    io.TextIOWrapper.flush: (LeanTranspilerPlugins.visit_textio_flush, True),
    sys.exit: (lambda self, node, vargs: f"IO.Process.exit {vargs[0]}", True),
}

FUNC_USINGS_MAP: Dict[Callable, str] = {}
