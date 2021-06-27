from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys

code_0: int = 0
code_1: int = 1
code_a: str = "a"
code_b: str = "b"
l_b: Set[str] = {code_a}
l_c: Dict[str, int] = {code_b: code_0}
if __name__ == "__main__":
    assert "a" in l_b
    print("OK")
