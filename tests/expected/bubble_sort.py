from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from typing import List


def bubble_sort(seq: List[int]) -> List[int]:
    L = len(seq)
    for _ in range(L):
        for n in range(1, L):
            if seq[n] < seq[n - 1]:
                if True:
                    __tmp1, __tmp2 = (seq[n], seq[n - 1])
                    seq[n - 1] = __tmp1
                    seq[n] = __tmp2
    return seq


if __name__ == "__main__":
    unsorted: List[int] = [14, 11, 19, 5, 16, 10, 19, 12, 5, 12]
    expected: List[int] = [5, 5, 10, 11, 12, 12, 14, 16, 19, 19]
    assert bubble_sort(unsorted) == expected
    print("OK")
