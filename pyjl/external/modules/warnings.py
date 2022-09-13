
import ast
from typing import Callable, Dict, Tuple, Union
import warnings

FuncType = Union[Callable, str]

class JuliaExternalModulePlugins():
    def visit_warnings_warn(self, node: ast.Call, vargs: list[str], kwargs: list[tuple[str,str]]):
        self._usings.add("Logging")
        if len(vargs) > 1:
            # Genera
            v0 = vargs[0][1:-1] if vargs[0].startswith("\"") else vargs[0]
            return f"@warn \"{vargs[1]}: {v0}\""
        return f"@warn {vargs[0]}"

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    warnings.warn: (JuliaExternalModulePlugins.visit_warnings_warn, True),
}

IGNORED_MODULE_SET = set([
    "warnings"
])