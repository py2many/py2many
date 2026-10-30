from dataclasses import dataclass
from enum import IntEnum
from typing import Generic, TypeVar, Union

T = TypeVar("T")
E = TypeVar("E", Exception, IntEnum)


@dataclass
class Ok(Generic[T]):
    value: T

    def is_ok(self) -> bool:
        return True

    def unwrap(self) -> T:
        return self.value

    def unwrap_or(self, default: T) -> T:
        return self.value


@dataclass
class Error(Generic[E]):
    error: E

    def is_ok(self) -> bool:
        return False

    def unwrap(self) -> T:
        raise Exception(self.error)

    def unwrap_or(self, default: T) -> T:
        return default


# std::result version
StdResult = Union[Ok[T], Error[E]]
# anyhow version (the error type is fixed by the backend)
Result = Union[Ok[T], Error[E]]
