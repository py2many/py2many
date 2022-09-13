import ast

from pyjl.helpers import pycall_import

try:
    import pyproj
except:
    pyproj = None

from typing import Callable, Dict, Tuple, Union

FuncType = Union[Callable, str]

class JuliaExternalModulePlugins():
    def visit_proj(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        pycall_import(self, node, "pyproj")
        kwargs_str = [f"{kw[0]}={kw[1]}" for kw in kwargs]
        if not vargs and not kwargs:
            return f"pyproj.Proj"
        elif not vargs and kwargs:
            return f"pyproj.Proj({', '.join(kwargs_str)})"
        return f"pyproj.Proj({', '.join(vargs)}, {', '.join(kwargs_str)})"

    def visit_transform(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        pycall_import(self, node, "pyproj")
        return f"pyproj.transform({', '.join(vargs)})" \
            if vargs else "pyproj.transform"

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    pyproj.Proj: (JuliaExternalModulePlugins.visit_proj, True),
    pyproj.transform: (JuliaExternalModulePlugins.visit_transform, True),
}

EXTERNAL_TYPE_MAP = {
    pyproj.Proj: lambda self: JuliaExternalModulePlugins.visit_proj(self, None, [], []),
    pyproj.transform: lambda self: JuliaExternalModulePlugins.visit_transform(self, None, [], []),
}

IGNORED_MODULE_SET = set([
    "pyproj"
])