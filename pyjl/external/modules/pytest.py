import ast
import pytest
from typing import Callable, Dict, Tuple, Union

FuncType = Union[Callable, str]

class JuliaExternalModulePlugins():
    def visit_raises(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        self._usings.add("Test")
        if len(vargs) == 2:
            return f"@test_throws {vargs[0]}, {vargs[1]}"
        if len(vargs) == 1:
            return f"@test_throws {vargs[0]}"
        return "@test_throws"

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    pytest.raises: (JuliaExternalModulePlugins.visit_raises, True),
}

IGNORED_MODULE_SET = {
    "pytest"
}
