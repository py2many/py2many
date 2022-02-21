from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from typing import List


def bisect_right(data: List[int], item: int) -> int:
    low: int = 0
    high: int = int(len(data))
    while low < high:
        middle: int = int((low + high) / 2)
        if item < data[middle]:
            high = middle
        else:
            low = middle + 1
    return low


def bin_it(limits: List[int], data: List[int]) -> List[int]:
    bins: List[int] = [0]
    for _x in limits:
        bins.append(0)
    for d in data:
        bins[bisect_right(limits, d)] += 1
    return bins


if __name__ == "__main__":
    limits: List[int] = [23, 37, 43, 53, 67, 83]
    data: List[int] = [
        95,
        21,
        94,
        12,
        99,
        4,
        70,
        75,
        83,
        93,
        52,
        80,
        57,
        5,
        53,
        86,
        65,
        17,
        92,
        83,
        71,
        61,
        54,
        58,
        47,
        16,
        8,
        9,
        32,
        84,
        7,
        87,
        46,
        19,
        30,
        37,
        96,
        6,
        98,
        40,
        79,
        97,
        45,
        64,
        60,
        29,
        49,
        36,
        43,
        55,
    ]
    assert bin_it(limits, data) == [11, 4, 2, 6, 9, 5, 13]
    print("OK")
