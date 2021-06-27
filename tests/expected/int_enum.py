from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from enum import IntEnum, IntFlag, auto


class Colors(IntEnum):
    RED = auto()
    GREEN = auto()
    BLUE = auto()


class Permissions(IntFlag):
    R: int = 1
    W: int = 2
    X: int = 16


def show():
    color_map: Dict[Colors, str] = {
        Colors.RED: "red",
        Colors.GREEN: "green",
        Colors.BLUE: "blue",
    }
    a: Colors = Colors.GREEN
    if a == Colors.GREEN:
        print("green")
    else:
        print("Not green")
    b: Permissions = Permissions.R
    if b == Permissions.R:
        print("R")
    else:
        print("Not R")
    assert len(color_map) != 0


if __name__ == "__main__":
    show()
