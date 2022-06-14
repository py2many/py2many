from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from argparse_dataclass import dataclass


@dataclass
class Options:
    v: bool = False
    n: int = 0


def fib(i: int) -> int:
    if i == 0 or i == 1:
        return 1
    return fib(i - 1) + fib(i - 2)


if __name__ == "__main__":
    args = Options.parse_args()
    if args.v:
        print("args.v is true")
    if args.n == 0:
        args.n: int = 5
    print(fib(args.n))
