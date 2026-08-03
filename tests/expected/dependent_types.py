from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from typing import Annotated

Uid = Annotated[int, lambda uid: 0 < uid < 1000]
Score = Annotated[int, lambda s: 0 <= s <= 100]


def main_func():
    u: Uid = 42
    s: Score = 85
    print(u)
    print(s)


if __name__ == "__main__":
    main_func()
