"""
This is an attempt to approximate some scenarios and 
translate Python exceptions into Julia exceptions.
Beware that translating exceptions is not straightforward. 
For instance, consider the following example:
    math.sqrt(-1)
This raises a ValueError in Python and a DomainError in Julia.
However, the following example also raises a ValueError in Python:
    float("-")
This raises an ArgumentError in Julia. Therefore, an exception 
in Python does not have a deterministic corresponding exception 
in Julia.
"""

import ast
import sys
from typing import Callable, Dict, Tuple, Union

class JuliaExternalModulePlugins():
    def visit_winerror(self, node: ast.Call, vargs: list[str], kwargs: list[str]):
        if vargs:
            return f"Base.windowserror({', '.join(vargs)})"
        elif getattr(node, "is_attr", None):
            return "Base.windowserror"
        return "Base.windowserror()"


FuncType = Union[Callable, str]

GENERIC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    # ErrorException is very generic
    RuntimeError: (
        lambda self, node, vargs, kwargs: f"ErrorException({', '.join(vargs)})",
        True,
    )
}

if sys.platform.startswith('win32'):
    EXTERNAL_TYPE_MAP = {
        WindowsError: "SystemError",
    }

    WIN_DISPATCH_TABLE = {
        # Exceptions
        WindowsError: (JuliaExternalModulePlugins.visit_winerror, True),
    }

    SMALL_DISPATCH_MAP = {
        "WindowsError.winerror": lambda n, vargs, kwargs: f"{vargs[0]}.errnum",
        "WindowsError.strerror": lambda n, vargs, kwargs: f"{vargs[0]}.prefix",
    }

    FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = GENERIC_DISPATCH_TABLE | WIN_DISPATCH_TABLE
else:
    FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = GENERIC_DISPATCH_TABLE
