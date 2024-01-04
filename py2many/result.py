from dataclasses import dataclass
from enum import IntEnum
from typing import Generic, TypeVar, Union

T = TypeVar("T")
E = TypeVar("E", Exception, IntEnum)


@dataclass
class Ok(Generic[T]):
    value: T


@dataclass
class Err(Generic[E]):
    error: E


Result = Union[Ok[T], Err[E]]
