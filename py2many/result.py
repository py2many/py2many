from typing import Optional, Generic, TypeVar
from dataclasses import dataclass
from enum import IntEnum

T = TypeVar("T")
E = TypeVar("E", Exception, IntEnum)


@dataclass
class Result(Generic[T, E]):
    data: Optional[T]
    error: Optional[E]


def Ok(t: T) -> Result[T, E]:
    return Result(t, None)


def Err(e: Exception, val: T = None) -> Result[T, E]:
    return Result(val, e)
