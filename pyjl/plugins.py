import sys
from typing import Callable, Dict, List, Tuple, Union


class JuliaTranspilerPlugins:
    def visit_range(self, node, vargs: List[str]) -> str:
        start = 0
        stop = 0
        step = None
        if len(vargs) == 1:
            stop = vargs[0]
        else:
            start = vargs[0]
            stop = vargs[1]
            if len(node.args) == 3:
                step = vargs[2]

        if step:
            return f"{start}:{step}:{stop}"

        return f"{start}:{stop}"

    def visit_print(self, node, vargs: List[str]) -> str:
        args = ", ".join(vargs)
        return f'println(join([{args}], " "))'

    def visit_cast_int(self, node, vargs) -> str:
        if not vargs:
            return "0"
        arg_type = self._typename_from_annotation(node.args[0])
        if arg_type is not None and arg_type.startswith("Float"):
            return f"Int64(floor({vargs[0]}))"
        return f"Int64({vargs[0]})"


# small one liners are inlined here as lambdas
SMALL_DISPATCH_MAP = {
    "str": lambda n, vargs: f"string({vargs[0]})" if vargs else '""',
    "len": lambda n, vargs: f"length({vargs[0]})",
    "enumerate": lambda n, vargs: f"{vargs[0]}.iter().enumerate()",
    "sum": lambda n, vargs: f"{vargs[0]}.iter().sum()",
    "bool": lambda n, vargs: f"Bool({vargs[0]})" if vargs else "false",
    # ::Int64 below is a hack to pass comb_sort.jl. Need a better solution
    "floor": lambda n, vargs: f"Int64(floor({vargs[0]}))",
}

SMALL_USINGS_MAP = {}

DISPATCH_MAP = {
    "range": JuliaTranspilerPlugins.visit_range,
    "xrange": JuliaTranspilerPlugins.visit_range,
    "print": JuliaTranspilerPlugins.visit_print,
    "int": JuliaTranspilerPlugins.visit_cast_int,
}

MODULE_DISPATCH_TABLE: Dict[str, str] = {}

CLASS_DISPATCH_TABLE = {}

ATTR_DISPATCH_TABLE = {}

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    sys.exit: (lambda self, node, vargs: f"quit({vargs[0]})", True),
}
