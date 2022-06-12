from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from ctypes import c_int16, c_int64, c_uint64


def main_func():
    a: c_int16 = c_int16(1)
    b = a.value
    print(b)
    c: c_int64 = c_int64(1)
    d = c.value
    print(d)
    e: c_uint64 = c_uint64(1)
    f = e.value
    print(f)


if __name__ == "__main__":
    main_func()
