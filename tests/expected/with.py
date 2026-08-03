from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys


class MockFile:

    def __init__(self, name):
        self.name = name
        self.closed: bool = False

    def __enter__(self):
        print(f"Opening {self.name}")
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> bool:
        print(f"Closing {self.name}")
        self.closed: bool = True
        return False

    def read(self) -> str:
        return "content"


def show():
    with MockFile("test.txt") as f:
        print(f.read())


if __name__ == "__main__":
    show()
