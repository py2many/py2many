import ast
import functools
from typing import Callable, Dict, Tuple, Union

from pyjl.helpers import pycall_import

FuncType = Union[Callable, str]

class JuliaExternalModulePlugins():
    def visit_partial(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        pycall_import(self, node, "functools")
        return f"functools.partial({', '.join(vargs)})"

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    functools.partial: (JuliaExternalModulePlugins.visit_partial, True),
}

IGNORED_MODULE_SET = set([
    "functools"
])