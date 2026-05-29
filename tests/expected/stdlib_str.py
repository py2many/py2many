from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys


def str_methods():
    s: str = "  Hello World  "
    print(s.lower())
    print(s.upper())
    print(s.capitalize())
    print(s.strip())
    print(s.lstrip())
    print(s.rstrip())
    parts = s.split()
    print(parts)
    joined = "-".join(["a", "b", "c"])
    print(joined)
    print(s.find("World"))
    print(s.replace("World", "Vlang"))
    if "123".isdigit():
        print("digit")
    if "abc".isalpha():
        print("alpha")
    if "   ".isspace():
        print("space")


if __name__ == "__main__":
    str_methods()
