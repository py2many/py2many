
import ast
import requests

from typing import Callable, Dict, Tuple, Union

FuncType = Union[Callable, str]

class JuliaExternalModulePlugins():
    def visit_get(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        self._usings.add("HTTP")
        return f"HTTP.get({', '.join(vargs)})"

    def visit_response_get(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        self._usings.add("HTTP")
        return f"String({vargs[0]}.body)"

    def visit_response_status_code(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        self._usings.add("HTTP")
        return f"{vargs[0]}.status"

    def visit_http_error(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        self._usings.add("HTTP")
        return f"HTTP.Exceptions.StatusError" \
            if not vargs else f"HTTP.Exceptions.StatusError({', '.join(vargs)})"

DISPATCH_MAP = {
    "requests.Response.status_code": JuliaExternalModulePlugins.visit_response_status_code
}

SMALL_DISPATCH_MAP = {
    "requests.codes.ok": lambda node, vargs, kwargs: "200"
}

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    requests.get: (JuliaExternalModulePlugins.visit_get, True),
    requests.Response.text: (JuliaExternalModulePlugins.visit_response_get, True),
}

IGNORED_MODULE_SET = set([
    "requests"
])

FUNC_TYPE_MAP = {
    requests.get: lambda self, node, vargs, kwargs: "requests.Response",
}

EXTERNAL_TYPE_MAP = {
    requests.HTTPError: lambda self: JuliaExternalModulePlugins.visit_http_error(self, None, [], [])
}
