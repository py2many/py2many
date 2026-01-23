import ast
import functools
from typing import Callable, Dict, List, Tuple, Union

from py2many.analysis import get_id

from .inference import V_WIDTH_RANK, get_inferred_v_type


class VTranspilerPlugins:
    def visit_sys_argv(self, node: ast.Attribute) -> str:
        self._usings.add("os")
        return "os.args"

    def visit_range(self, node: ast.Call, vargs: List[str]) -> str:
        if len(node.args) == 1:
            return f"[]int{{len: {vargs[0]}, init: it}}"
        elif len(node.args) == 2:
            return f"[]int{{len: {vargs[1]} - {vargs[0]}, init: it + {vargs[0]}}}"
        elif len(node.args) == 3:
            # Step is not easily supported in array init, fallback to range
            return f"({vargs[0]}..{vargs[1]})"

        raise Exception(
            f"encountered range() call with unknown parameters: range({vargs})"
        )

    def visit_print(self, node: ast.Call, vargs: List[str]) -> str:
        args: List[str] = []
        total_args: List[str] = []
        for arg in node.args:
            if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                args.append(arg.value.replace("'", ""))
            elif get_inferred_v_type(arg) == "string":
                args.append(f"${{{self.visit(arg)}}}")
            else:
                if args:
                    total_args.append(f"'{' '.join(args)}'")
                    args = []
                total_args.append(f"({self.visit(arg)}).str()")
        if args:
            total_args.append(f"'{' '.join(args)}'")
        total_args = " + ' ' + ".join(total_args)

        return f"println({total_args})"

    def visit_bool(self, node: ast.Call, vargs: List[str]) -> str:
        if not vargs:
            return "false"
        if get_inferred_v_type(node.args[0]) in V_WIDTH_RANK:
            return f"{self.visit(node.args[0])} != 0"
        else:
            return f"({self.visit(node.args[0])}).bool()"

    @staticmethod
    def visit_cast(node, vargs, cast_to: str) -> str:
        if not vargs:
            if cast_to in ("i32", "int"):
                return "0"
            elif cast_to == "f64":
                return "0.0"

        # Check if argument is Any or a sum type (heuristically)
        # We can't easily check inferred type here without access to self or scopes in staticmethod
        # But we can check if it looks like a variable (which might be Any in lambdas)
        if cast_to in ("int", "f64"):
            # If it's a direct variable name (likely Any in our test case), use `as`
            # This is a heuristic. Ideally we'd check get_inferred_v_type(node.args[0])
            # But this method is static.
            # Better to inspect the node argument directly if possible or update signature.
            pass
        return f"{cast_to}({vargs[0]})"

    def visit_int(self, node: ast.Call, vargs: List[str]) -> str:
        # Placeholder for post-processing in VTranspiler.visit_Module
        # Converts int(x) to (x as int) for Any/Sum types
        return f"CAST_INT({vargs[0]})"

    def visit_min_max(self, node: ast.Call, vargs: List[str]) -> str:
        self._usings.add("arrays")
        func = "min" if get_id(node.func) == "min" else "max"
        # Since python allows calling min/max on either a container or
        # multiple integers while V only allows containers, the latter case
        # is turned to a container when passing it to the V side.
        if len(vargs) == 1:
            return f"arrays.{func}({vargs[0]}) or {{ panic('!') }}"
        else:
            return f"arrays.{func}([{', '.join(vargs)}]) or {{ panic('!') }}"

    def visit_sorted(self, node: ast.Call, vargs: List[str]) -> str:
        # V's sort is in-place, so we clone, sort and return
        return f"(fn (a []Any) []Any {{ mut b := a.clone(); b.sort(); return b }}({vargs[0]}))"

    def visit_enumerate(self, node: ast.Call, vargs: List[str]) -> str:
        # V doesn't have enumerate outside of for loops easily
        # This is a placeholder for when it's used as an expression
        return f"{vargs[0]} /* enumerate is usually used in for loops in V */"

    def visit_zip(self, node: ast.Call, vargs: List[str]) -> str:
        # Placeholder for zip
        return f"/* zip({', '.join(vargs)}) not fully supported as expression */"

    def visit_open(self, node: ast.Call, vargs: List[str]) -> str:
        self._usings.add("os")
        if len(vargs) > 1:
            mode = vargs[1].replace("'", "").replace('"', "")
            if "w" in mode:
                return f"os.create({vargs[0]}) or {{ panic(err) }}"
        return f"os.open({vargs[0]}) or {{ panic(err) }}"


SMALL_DISPATCH_MAP: Dict[str, Callable] = {
    "str": lambda n, vargs: f"({vargs[0]}).str()" if vargs else '""',
    "floor": lambda n, vargs: f"int(math.floor({vargs[0]}))",
    "float": functools.partial(VTranspilerPlugins.visit_cast, cast_to="f64"),
    "len": lambda n, vargs: f"{vargs[0]}.len",
    "sys.exit": lambda n, vargs: f"exit({vargs[0] if vargs else '0'})",
    "all": lambda n, vargs: f"{vargs[0]}.all(it)",
    "any": lambda n, vargs: f"{vargs[0]}.any(it)",
    "abs": lambda n, vargs: f"math.abs({vargs[0]})",
    "round": lambda n, vargs: f"math.round({vargs[0]})",
    "pow": lambda n, vargs: f"math.pow({vargs[0]}, {vargs[1]})",
    "sum": lambda n, vargs: f"arrays.sum({vargs[0]}) or {{ 0 }}",
    "input": lambda n, vargs: f"os.input({vargs[0] if vargs else ''})",
    "type": lambda n, vargs: f"typeof({vargs[0]}).name",
    "id": lambda n, vargs: f"ptr_str({vargs[0]})",
    "isinstance": lambda n, vargs: f"{vargs[0]} is {vargs[1]}",
    "list": lambda n, vargs: f"{vargs[0]}" if vargs else "[]",
    "tuple": lambda n, vargs: f"{vargs[0]}" if vargs else "[]",
    "set": lambda n, vargs: f"{vargs[0]}" if vargs else "[]",
    "dict": lambda n, vargs: f"{vargs[0]}" if vargs else "{}",
    "getattr": lambda n, vargs: f"/* getattr({', '.join(vargs)}) not supported */",
    "setattr": lambda n, vargs: f"/* setattr({', '.join(vargs)}) not supported */",
    "hasattr": lambda n, vargs: f"/* hasattr({', '.join(vargs)}) not supported */",
    "os.path.exists": lambda n, vargs: f"os.exists({vargs[0]})",
    "os.remove": lambda n, vargs: f"os.rm({vargs[0]}) or {{ panic(err) }}",
    "NamedTemporaryFile": lambda n, vargs: "os.create(os.join_path(os.temp_dir(), 'temp_file')) or { panic(err) }",
    "tempfile.NamedTemporaryFile": lambda n, vargs: "os.create(os.join_path(os.temp_dir(), 'temp_file')) or { panic(err) }",
}

SMALL_USINGS_MAP: Dict[str, str] = {
    "floor": "math",
    "abs": "math",
    "round": "math",
    "pow": "math",
    "sum": "arrays",
    "input": "os",
}

DISPATCH_MAP: Dict[str, Callable] = {}

MODULE_DISPATCH_TABLE: Dict[str, str] = {}

DECORATOR_DISPATCH_TABLE: Dict[str, Callable] = {}

CLASS_DISPATCH_TABLE: Dict[str, Callable] = {}

AttrType = Union[type, str]

ATTR_DISPATCH_TABLE: Dict[AttrType, Callable] = {
    "sys.argv": VTranspilerPlugins.visit_sys_argv,
}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    range: (VTranspilerPlugins.visit_range, False),
    print: (VTranspilerPlugins.visit_print, False),
    bool: (VTranspilerPlugins.visit_bool, False),
    int: (VTranspilerPlugins.visit_int, False),
    min: (VTranspilerPlugins.visit_min_max, False),
    max: (VTranspilerPlugins.visit_min_max, False),
    map: (lambda self, node, vargs: f"{vargs[1]}.map({vargs[0]})", False),
    filter: (lambda self, node, vargs: f"{vargs[1]}.filter({vargs[0]})", False),
    sorted: (VTranspilerPlugins.visit_sorted, False),
    enumerate: (VTranspilerPlugins.visit_enumerate, False),
    zip: (VTranspilerPlugins.visit_zip, False),
    open: (VTranspilerPlugins.visit_open, True),
    "functools.reduce": (
        lambda self, node, vargs: f"{vargs[1]}.reduce({vargs[0]})",
        False,
    ),
    "functools.partial": (
        lambda self, node, vargs: f"/* partial({', '.join(vargs)}) not supported */",
        False,
    ),
    "functools.lru_cache": (
        lambda self, node, vargs: "/* lru_cache not supported */",
        False,
    ),
    "divmod": (
        lambda self, node, vargs: f"({vargs[0]} / {vargs[1]}, {vargs[0]} % {vargs[1]})",
        False,
    ),
}
