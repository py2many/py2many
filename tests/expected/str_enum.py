from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from enum import Enum


class Colors(str, Enum):
    RED: str = "red"
    GREEN: str = "green"
    BLUE: str = "blue"


def show():
    color_map: Dict[Colors, str] = {
        Colors.RED: "1",
        Colors.GREEN: "2",
        Colors.BLUE: "3",
    }
    a: Colors = Colors.GREEN
    if a == Colors.GREEN:
        print("green")
    else:
        print("Not green")
    print(len(color_map))


if __name__ == "__main__":
    show()
