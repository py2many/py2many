from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from typing import List


def inline_pass():
    pass


def inline_ellipsis():
    ...


def indexing() -> int:
    sum: int = 0
    a: List[int] = []
    for i in range(10):
        a.append(i)
        sum += a[i]
    return sum


def infer_bool(code: int) -> bool:
    return code in [1, 2, 4]


def show():
    a1: int = 10
    if True:
        b1: int = 15
        b2: int = 15
    assert b1 == 15
    assert b2 == 15
    b9: int = 2
    b10: int = 2
    assert b9 == b10
    a2: float = 2.1
    print(a2)
    for i in range(0, 10):
        print(i)
    for i in range(0, 10, 2):
        print(i)
    a3: int = -a1
    a4: int = a3 + a1
    print(a4)
    t1 = 10 if a1 > 5 else 5
    assert t1 == 10
    sum1: int = indexing()
    print(sum1)
    a5: List[int] = [1, 2, 3]
    print(len(a5))
    a9: List[str] = ["a", "b", "c", "d"]
    print(len(a9))
    a7: Dict[str, int] = {"a": 1, "b": 2}
    print(len(a7))
    a8: bool = True
    if a8:
        print("true")
    elif a4 > 0:
        print("never get here")
    if a1 == 11:
        print("false")
    else:
        print("true")
    if 1 != None:
        print("World is sane")
    print("True" if True else "False")
    if True:
        a1 += 1
    assert a1 == 11
    if True:
        print("true")
    inline_pass()
    s: str = "1    2"
    print(s)
    assert infer_bool(1)
    _escape_quotes: str = ' foo "bar" baz '
    assert "bbc" in "aaabbccc"
    assert bool(1)
    2
    (_c1, _c2) = (1, 3)


if __name__ == "__main__":
    show()
