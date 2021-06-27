from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys


def compare_assert(a: int, b: int):
    assert a == b
    assert not 0 == 1


if __name__ == "__main__":
    assert True
    assert not False
    compare_assert(1, 1)
    assert True, 1
    assert True, "message"
    print("OK")
