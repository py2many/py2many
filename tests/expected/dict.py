from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys


def implicit_keys() -> bool:
    CODES: Dict[str, int] = {"KEY": 1}
    return "KEY" in CODES


def explicit_keys() -> bool:
    CODES: Dict[str, int] = {"KEY": 1}
    return "KEY" in CODES.keys()


def dict_values() -> bool:
    CODES: Dict[str, int] = {"KEY": 1}
    return 1 in CODES.values()


def return_dict_index_str(key: str) -> int:
    CODES: Dict[str, int] = {"KEY": 1}
    return CODES[key]


def return_dict_index_int(key: int) -> str:
    CODES: Dict[int, str] = {1: "one"}
    return CODES[key]


if __name__ == "__main__":
    assert implicit_keys()
    assert explicit_keys()
    assert dict_values()
    assert return_dict_index_str("KEY") == 1
    assert return_dict_index_int(1) == "one"
    print("OK")
