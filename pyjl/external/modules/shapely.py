import ast

try:
    from shapely.geometry.base import BaseGeometry
    from shapely.ops import transform
except:
    shapely = None

from typing import Callable, Dict, Optional, Tuple, Union

FuncType = Union[Callable, str]

class JuliaExternalModulePlugins():
    def visit_basegeometry(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        JuliaExternalModulePlugins._pycall_import(self, "shapely.geometry.base", "shapely_geo_base")
        return f"shapely_geo_base.BaseGeometry({', '.join(vargs)})"

    def visit_transform(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        JuliaExternalModulePlugins._pycall_import(self, "shapely.ops", "shapely_ops")
        return f"shapely_ops.transform({', '.join(vargs)})"

    def _pycall_import(self, mod_name: str, opt_name: Optional[str] = None):
        self._usings.add("PyCall")
        if opt_name:
            import_stmt = f'{opt_name} = pyimport("{mod_name}")'
        else:
            import_stmt = f'{mod_name} = pyimport("{mod_name}")'
        self._globals.add(import_stmt)

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    BaseGeometry: (JuliaExternalModulePlugins.visit_basegeometry, True),
    transform: (JuliaExternalModulePlugins.visit_transform, True),
}

IGNORED_MODULE_SET = set([
    "shapely",
    "shapely.geometry.base",
    "shapely.ops",
])