import ast
import time
from typing import Callable, Dict, Tuple, Union


class JuliaExternalModulePlugins:
    def visit_ctime(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        JuliaExternalModulePlugins._visit_time(self)
        # Format date to Python format
        return f"Dates.format(Dates.epochms2datetime({vargs[0]}), Dates.RFC1123Format)"

    def visit_time(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        JuliaExternalModulePlugins._visit_time(self)
        return f"Dates.datetime2unix(Dates.now())"

    def _visit_time(self):
        self._usings.add("Dates")


FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    time.ctime: (JuliaExternalModulePlugins.visit_ctime, False),
    time.time: (JuliaExternalModulePlugins.visit_time, False),
}
