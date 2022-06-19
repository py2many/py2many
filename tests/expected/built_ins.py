from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys


def default_builtins():
    a: str = str()
    b: bool = bool()
    c: int = int()
    d: float = float()
    assert a == ""
    assert b == False
    assert c == 0
    assert d == 0.0


if __name__ == "__main__":
    a: int = max(1, 2)
    print(a)
    b: int = min(1, 2)
    print(b)
    c: int = int(min(1.0, 2.0))
    print(c)
