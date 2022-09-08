import ast

try:
    import pyproj
except:
    pyproj = None

from typing import Callable, Dict, Tuple, Union

FuncType = Union[Callable, str]

class JuliaExternalModulePlugins():
    def visit_proj(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        JuliaExternalModulePlugins._pycall_import(self, "pyproj")
        return f"pyproj.Proj({', '.join(vargs)})"

    def visit_transform(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        JuliaExternalModulePlugins._pycall_import(self, "pyproj")
        return f"pyproj.transform({', '.join(vargs)})"

    def _pycall_import(self, mod_name: str):
        self._usings.add("PyCall")
        import_stmt = f'{mod_name} = pyimport("{mod_name}")'
        self._globals.add(import_stmt)

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    pyproj.Proj: (JuliaExternalModulePlugins.visit_proj, True),
    pyproj.transform: (JuliaExternalModulePlugins.visit_transform, True),
}

IGNORED_MODULE_SET = set([
    "pyproj"
])