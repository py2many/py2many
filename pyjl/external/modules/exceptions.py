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

from typing import Callable, Dict, Tuple, Union


FuncType = Union[Callable, str]

FUNC_DISPATCH_TABLE: Dict[FuncType, Tuple[Callable, bool]] = {
    # ErrorException is very generic
    RuntimeError: (
        lambda self, node, vargs, kwargs: f"ErrorException({', '.join(vargs)})",
        True,
    )
}
