from typing import TypeVar, Generic, Union
from dataclasses import dataclass
from enum import IntEnum

T = TypeVar("T")
E = TypeVar("E", Exception, IntEnum)


@dataclass
class Ok(Generic[T]):
    value: T


@dataclass
class Err(Generic[E]):
    error: E


Result = Union[Ok[T], Err[E]]
