from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from typing import List


def test_python(iterations: int):
    iteration: int = 0
    total: float = float(0.0)
    array_length: int = 1000
    array: List[int] = [i for i in range(array_length)]
    print("iterations", iterations)
    while iteration < iterations:
        innerloop: int = 0
        while innerloop < 100:
            total += array[(iteration + innerloop) % array_length]
            innerloop += 1
        iteration += 1
    if total == 15150:
        print("OK")
    del array


if __name__ == "__main__":
    test_python(3)
