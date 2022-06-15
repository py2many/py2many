from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys


def complex_test():
    c1: complex = 2 + 3.0j
    c2: complex = 4 + 5.0j
    c3: complex = c1 + c2
    assert c3 == 6 + 8.0j
    c4: complex = c1 + 3
    assert c4 == 5 + 3.0j
    c5: complex = c1 + 4.0j
    assert c5 == 2 + 7.0j
    c6: complex = c3 - 2.3
    assert c6 == 3.7 + 8.0j


if __name__ == "__main__":
    complex_test()
    print("OK")
