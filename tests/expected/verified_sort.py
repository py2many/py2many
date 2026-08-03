from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from dataclasses import dataclass
from typing import List
from py2many.spec import CHECKER
from py2many.theorem import by, lemma, theorem


@dataclass
class BankAccount:
    balance: int

    def deposit(self, amount: int) -> "BankAccount":
        return BankAccount(self.balance + amount)


def safe_sqrt(n: int) -> int:
    i: int = 0
    while i * i <= n:
        i += 1
    return i - 1


@lemma
@by("native_decide")
def sqrt_of_9() -> bool:
    return safe_sqrt(9) == 3


def merge(left: List[int], right: List[int]) -> List[int]:
    result: List[int] = []
    i: int = 0
    j: int = 0
    while i < len(left) and j < len(right):
        if left[i] <= right[j]:
            result.append(left[i])
            i += 1
        else:
            result.append(right[j])
            j += 1
    while i < len(left):
        result.append(left[i])
        i += 1
    while j < len(right):
        result.append(right[j])
        j += 1
    return result


def take(xs: List[int], n: int) -> List[int]:
    out: List[int] = []
    i: int = 0
    while i < n:
        out.append(xs[i])
        i += 1
    return out


def drop(xs: List[int], n: int) -> List[int]:
    out: List[int] = []
    i: int = n
    while i < len(xs):
        out.append(xs[i])
        i += 1
    return out


def sort_u64(arr: List[int]) -> List[int]:
    if len(arr) <= 1:
        return arr
    mid: int = len(arr) // 2
    left: List[int] = sort_u64(take(arr, mid))
    right: List[int] = sort_u64(drop(arr, mid))
    return merge(left, right)


@by("native_decide")
@theorem
def concrete_example() -> bool:
    return sort_u64([3, 1, 4, 1, 5, 9, 2, 6]) == [1, 1, 2, 3, 4, 5, 6, 9]


if __name__ == "__main__":
    acct: BankAccount = BankAccount(10)
    print("OK")
