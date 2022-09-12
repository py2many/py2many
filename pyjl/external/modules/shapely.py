import ast

from pyjl.helpers import pycall_import

try:
    from shapely.geometry.base import BaseGeometry
    from shapely.ops import transform
except:
    shapely = None

from typing import Callable, Dict, Optional, Tuple, Union

FuncType = Union[Callable, str]

class JuliaExternalModulePlugins():
    def visit_basegeometry(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        pycall_import(self, node, "shapely.geometry.base", "shapely_geo_base")
        return f"shapely_geo_base.BaseGeometry({', '.join(vargs)})"

    def visit_transform(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        pycall_import(self, node, "shapely.ops", "shapely_ops")
        return f"shapely_ops.transform({', '.join(vargs)})"

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    BaseGeometry: (JuliaExternalModulePlugins.visit_basegeometry, True),
    transform: (JuliaExternalModulePlugins.visit_transform, True),
}

IGNORED_MODULE_SET = set([
    "shapely",
    "shapely.geometry.base",
    "shapely.ops",
])