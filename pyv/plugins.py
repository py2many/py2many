import ast
from typing import List

from .inference import get_inferred_v_type, V_WIDTH_RANK


class VTranspilerPlugins:
    def visit_sys_argv(self, node):
        self._usings.add("os")
        return "os.args"

    def visit_range(self, node, vargs: List[str]) -> str:
        if len(node.args) == 1:
            return f"0..{vargs[0]}"
        elif len(node.args) == 2:
            return f"{vargs[0]}..{vargs[1]}"

        raise Exception(
            "encountered range() call with unknown parameters: range({})".format(vargs)
        )

    def visit_print(self, node, vargs: List[str]) -> str:
        args = []
        total_args = []
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

    def visit_bool(self, node, vargs) -> str:
        if get_inferred_v_type(node.args[0]) in V_WIDTH_RANK:
            return f"{self.visit(node.args[0])} != 0"
        else:
            return f"({self.visit(node.args[0])}).bool()"


SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs: f"({vargs[0]}).str()",
    "floor": lambda n, vargs: f"int(floor({vargs[0]}))",
    "len": lambda n, vargs: f"{vargs[0]}.len",
    "sys.exit": lambda n, vargs: f"exit({vargs[0] if vargs else '0'})",
}

SMALL_USINGS_MAP = {}

DISPATCH_MAP = {}

MODULE_DISPATCH_TABLE = {}

DECORATOR_DISPATCH_TABLE = {}

CLASS_DISPATCH_TABLE = {}

ATTR_DISPATCH_TABLE = {
    "sys.argv": VTranspilerPlugins.visit_sys_argv,
}

FUNC_DISPATCH_TABLE = {
    range: (VTranspilerPlugins.visit_range, False),
    print: (VTranspilerPlugins.visit_print, False),
    bool: (VTranspilerPlugins.visit_bool, False),
}
