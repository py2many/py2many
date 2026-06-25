from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys


def sum_all(*nums: int) -> int:
    total: int = 0
    for n in nums:
        total += n
    return total


def main_func():
    print("a" * 5)
    print([0] * 3)
    numbers: list[int] = [1, 2, 3]
    print(sum_all(*numbers))
    others: list[int] = [4, 5]
    all_nums: list[int] = [0, *numbers, *others, 6]
    print(all_nums)
    data: list[int] = [10, 20, 30, 40, 50]
    a: int
    rest: list[int]
    e: int
    a, *rest, e = data
    print(a)
    print(rest)
    print(e)


if __name__ == "__main__":
    main_func()
