from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys


def compare_with_integer_variable():
    i: int = 0
    s: int = 1
    if i:
        s = 2
    else:
        s = 3
    assert s == 3


def use_zero_for_comparison():
    i: int = 0
    s: int = 1
    if 0:
        s = 2
    else:
        s = 3
    assert s == 3


if __name__ == "__main__":
    compare_with_integer_variable()
    use_zero_for_comparison()
    print("OK")
