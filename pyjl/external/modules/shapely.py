import ast

from pyjl.helpers import pycall_import

try:
    from shapely.geometry.base import BaseGeometry
    from shapely.geometry import Point
    from shapely.ops import transform
except:
    shapely = None

from typing import Callable, Dict, Optional, Tuple, Union

FuncType = Union[Callable, str]

class JuliaExternalModulePlugins():
    def visit_basegeometry(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        pycall_import(self, node, "shapely.geometry.base", "shapely_geo_base")
        return f"shapely_geo_base.BaseGeometry({', '.join(vargs)})" \
            if vargs else "shapely_geo_base.BaseGeometry"

    def visit_transform(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        pycall_import(self, node, "shapely.ops", "shapely_ops")
        return f"shapely_ops.transform({', '.join(vargs)})"
    
    def visit_point(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        pycall_import(self, node, "shapely.geometry", "shapely_geo")
        return f"shapely_geo.Point({', '.join(vargs)})" \
            if vargs else "shapely_geo.Point"

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    BaseGeometry: (JuliaExternalModulePlugins.visit_basegeometry, True),
    transform: (JuliaExternalModulePlugins.visit_transform, True),
    Point: (JuliaExternalModulePlugins.visit_point, True),
}

IGNORED_MODULE_SET = set([
    "shapely",
    "shapely.geometry",
    "shapely.geometry.base",
    "shapely.ops",
])

EXTERNAL_TYPE_MAP = {
    BaseGeometry: lambda self: JuliaExternalModulePlugins.visit_basegeometry(self, None, [], []),
    Point: lambda self: JuliaExternalModulePlugins.visit_point(self, None, [], []),
}
