from py2many.analysis import IGNORED_MODULE_SET
import pytest
from typing import Callable, Dict, Tuple, Union

FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    pytest.raises: (lambda self, node, vargs, kwargs: f"throw({', '.join(vargs)})" 
        if len(vargs) > 0 else "throw", True),
}

IGNORED_MODULE_SET = {
    "pytest"
}
