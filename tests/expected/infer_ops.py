from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from ctypes import (
    c_int8,
    c_int16,
    c_int32,
    c_int64,
    c_uint8,
    c_uint16,
    c_uint32,
    c_uint64,
)


def foo():
    a: int = 10
    b: int = 20
    _c1: int = a + b
    _c2: int = a - b
    _c3: int = a * b
    _c4: float = a / b
    _c5: int = -a
    d: float = 2.0
    _e1: float = a + d
    _e2: float = a - d
    _e3: float = a * d
    _e4: float = a / d
    _f: float = -3.0
    _g: int = -a


def add1(x: c_int8, y: c_int8) -> c_int16:
    return x + y


def add2(x: c_int16, y: c_int16) -> c_int32:
    return x + y


def add3(x: c_int32, y: c_int32) -> c_int64:
    return x + y


def add4(x: c_int64, y: c_int64) -> c_int64:
    return x + y


def add5(x: c_uint8, y: c_uint8) -> c_uint16:
    return x + y


def add6(x: c_uint16, y: c_uint16) -> c_uint32:
    return x + y


def add7(x: c_uint32, y: c_uint32) -> c_uint64:
    return x + y


def add8(x: c_uint64, y: c_uint64) -> c_uint64:
    return x + y


def add9(x: c_int8, y: c_uint16) -> c_uint32:
    return x + y


def sub(x: c_int8, y: c_int8) -> c_int8:
    return x - y


def mul(x: c_int8, y: c_int8) -> c_int16:
    return x * y


def fadd1(x: c_int8, y: float) -> float:
    return x + y


def show():
    assert fadd1(6, 6.0) == 12
    print("OK")


if __name__ == "__main__":
    foo()
    show()
