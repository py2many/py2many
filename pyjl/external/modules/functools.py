import ast
import functools
from typing import Callable, Dict, Tuple, Union

FuncType = Union[Callable, str]

class JuliaExternalModulePlugins():
    def visit_partial(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        JuliaExternalModulePlugins._pycall_import(self, "functools")
        return f"functools.partial({', '.join(vargs)})"

    def _pycall_import(self, mod_name: str):
        self._usings.add("PyCall")
        import_stmt = f'{mod_name} = pyimport("{mod_name}")'
        self._globals.add(import_stmt)

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    functools.partial: (JuliaExternalModulePlugins.visit_partial, True),
}

IGNORED_MODULE_SET = set([
    "functools"
])