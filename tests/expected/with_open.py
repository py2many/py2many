from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from tempfile import NamedTemporaryFile

if __name__ == "__main__":
    with NamedTemporaryFile(mode="a+", delete=False) as temp_file:
        file_path = temp_file.name
        with open(file_path, "w") as f:
            f.write("hello")
        with open(file_path, "r") as f:
            assert f.read(1) == "h"
            assert f.read() == "ello"
            print("OK")
