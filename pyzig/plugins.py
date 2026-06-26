import ast
import random
import time
from typing import Callable, Dict, List, Tuple, Union

from py2many.analysis import get_id


def _arg_is_str(transpiler, n) -> bool:
    """Whether a print argument prints as a zig string (needs ``{s}``)."""
    if transpiler._generic_typename_from_annotation(n) == "str":
        return True
    # Indexing a List[str] (e.g. argv[1]) yields a string element.
    if isinstance(n, ast.Subscript) and isinstance(n.value, ast.Name):
        scopes = getattr(n.value, "scopes", None)
        var = scopes.find(get_id(n.value)) if scopes is not None else None
        ann = getattr(var, "annotation", None)
        if isinstance(ann, ast.Subscript):
            elt = ann.slice
            if isinstance(elt, ast.Index):
                elt = elt.value
            return get_id(elt) == "str"
    # IfExp with string constants (from PrintBoolRewriter: 'True' if x else 'False')
    if isinstance(n, ast.IfExp):
        if isinstance(n.body, ast.Constant) and isinstance(n.body.value, str):
            return True
    return False


class ZigTranspilerPlugins:
    @staticmethod
    def visit_cast(node, vargs, cast_to: str) -> str:
        if not vargs:
            if cast_to == "Float64":
                return "0.0"
        return f"{cast_to}({vargs[0]})"

    def visit_int(self, node, vargs: List[str]) -> str:
        if not vargs:
            return "0"
        # Determine if the argument is a float or int
        arg = node.args[0] if node.args else None
        if arg:
            ann = self._generic_typename_from_annotation(arg)
            if ann in ("float", "f64", "f32"):
                return f"@as(i32, @intFromFloat({vargs[0]}))"
            # Check if the argument is a literal float
            if isinstance(arg, ast.Constant) and isinstance(arg.value, float):
                return f"@as(i32, @intFromFloat({vargs[0]}))"
            # Check if it's a function call that might return float (like min/max with float args)
            if isinstance(arg, ast.Call):
                # If any arg of the inner call is float, assume float result
                for inner_arg in arg.args:
                    if isinstance(inner_arg, ast.Constant) and isinstance(
                        inner_arg.value, float
                    ):
                        return f"@as(i32, @intFromFloat({vargs[0]}))"
        return f"@intCast({vargs[0]})"

    def visit_print(self, node, vargs: List[str]) -> str:
        placeholders = []
        for n in node.args:
            placeholders.append("{s}" if _arg_is_str(self, n) else "{}")
        # Python's print writes to stdout; std.debug.print writes to stderr, so
        # emit a stdout helper instead (defined by ZigTranspiler.aliases()).
        self._uses_print = True
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
    "len": lambda n, vargs: f"{vargs[0]}.len",
    "str": lambda n, vargs: (
        f'std.fmt.allocPrint(std.heap.page_allocator, "{{d}}", .{{{vargs[0]}}})'
        if vargs
        else '""'
    ),
    "bool": lambda n, vargs: f"({vargs[0]} != 0)" if vargs else "false",
    "int": lambda n, vargs: "0",
    "floor": lambda n, vargs: f"@as(i32, @intFromFloat(@floor({vargs[0]})))",
    "float": lambda n, vargs: (
        f"@as(f64, @floatFromInt({vargs[0]}))" if vargs else "0.0"
    ),
    "max": lambda n, vargs: f"@max({', '.join(vargs)})",
    "min": lambda n, vargs: f"@min({', '.join(vargs)})",
    "abs": lambda n, vargs: f"@abs({vargs[0]})",
}

SMALL_USINGS_MAP: Dict[str, str] = {}

DISPATCH_MAP = {
    "print": ZigTranspilerPlugins.visit_print,
    "range": ZigTranspilerPlugins.visit_range,
    "int": ZigTranspilerPlugins.visit_int,
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
