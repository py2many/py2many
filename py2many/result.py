from dataclasses import dataclass
from enum import IntEnum
from typing import Generic, TypeVar, Union

T = TypeVar("T")
E = TypeVar("E", Exception, IntEnum)


@dataclass
class Ok(Generic[T]):
    value: T


@dataclass
class Error(Generic[E]):
    error: E


# std::result version
StdResult = Union[Ok[T], Error[E]]
# anyhow version
Result = Ok[T]
