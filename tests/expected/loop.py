from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys


def for_with_break():
    for i in range(4):
        if i == 2:
            break
        print(i)


def for_with_continue():
    for i in range(4):
        if i == 2:
            continue
        print(i)


def for_with_else():
    for i in range(4):
        print(i)
    else:
        print("OK")


def while_with_break():
    i: int = 0
    while True:
        if i == 2:
            break
        print(i)
        i += 1


def while_with_continue():
    i: int = 0
    while i < 5:
        i += 1
        if i == 2:
            continue
        print(i)


if __name__ == "__main__":
    for_with_break()
    for_with_continue()
    for_with_else()
    while_with_break()
    while_with_continue()
