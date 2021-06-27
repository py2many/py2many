from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from typing import List


def main_func():
    ands: List[bool] = []
    ors: List[bool] = []
    xors: List[bool] = []
    for a in [False, True]:
        for b in [False, True]:
            ands.append(a & b)
            ors.append(a | b)
            xors.append(a ^ b)
    assert ands == [False, False, False, True]
    assert ors == [False, True, True, True]
    assert xors == [False, True, True, False]
    print("OK")


if __name__ == "__main__":
    main_func()
