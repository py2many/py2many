from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys


def show():
    my_list: List[int] = [1, 2, 3, 4, 5]
    del my_list[2]
    print(len(my_list))
    my_dict: Dict[str, int] = {"a": 1, "b": 2, "c": 3}
    del my_dict["b"]
    print(len(my_dict))


if __name__ == "__main__":
    show()
