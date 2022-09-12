import ast
from pyjl.helpers import pycall_import
import requests_mock
from typing import Callable, Dict, Tuple, Union

FuncType = Union[Callable, str]

class JuliaExternalModulePlugins():
    def visit_mock(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        pycall_import(self, node, "requests_mock")
        return "requests_mock.mock()"
    
    def visit_mocker_get(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        pycall_import(self, node, "requests_mock")
        func_name = vargs[0]
        if hasattr(node, "orig_name"):
            func_name = node.orig_name
        kwargs_str = [f"{kw[0]}={kw[1]}" for kw in kwargs]
        return f"{func_name}({', '.join(vargs[1:])}, {', '.join(kwargs_str)})"

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    requests_mock.mock: (JuliaExternalModulePlugins.visit_mock, True),
    requests_mock.Mocker.get: (JuliaExternalModulePlugins.visit_mocker_get, True),
    # requests_mock.mock.get
}

IGNORED_MODULE_SET = {
    "requests_mock"
}

FUNC_TYPE_MAP = {
    requests_mock.mock: lambda self, node, vargs, kwargs: "requests_mock.Mocker",
}