from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from tempfile import NamedTemporaryFile

if __name__ == "__main__":
    if True:
        temp_file = NamedTemporaryFile(mode="a+", delete=False)
        file_path = temp_file.name
        if True:
            f = open(file_path, "w")
            f.write("hello")
        if True:
            f = open(file_path, "r")
            assert f.read(1) == "h"
            assert f.read() == "ello"
            print("OK")
