from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
import re


def test_re_methods():
    text: str = "The quick brown fox jumps over the lazy dog"
    search_res = re.search("fox", text)
    if search_res:
        print("Found fox")
    match_res = re.match("The", text)
    if match_res:
        print("Matched The")
    findall_res = re.findall("\\w+", text)
    print(len(findall_res))
    sub_res = re.sub("fox", "cat", text)
    print(sub_res)
    split_res = re.split("\\s+", text)
    print(len(split_res))
    pattern = re.compile("\\d+")
    print("Pattern compiled")


if __name__ == "__main__":
    test_re_methods()
