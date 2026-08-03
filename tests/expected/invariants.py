from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from dataclasses import dataclass
from py2many.smt import invariant
from py2many.smt import pre as smt_pre


@dataclass
class BankAccount:
    balance: int
    if invariant:
        balance >= 0

    def deposit(self, amount: int) -> "BankAccount":
        if smt_pre:
            amount > 0
        return BankAccount(self.balance + amount)


def main_func():
    acct: BankAccount = BankAccount(10)
    acct2 = acct.deposit(5)
    print(acct2.balance)


if __name__ == "__main__":
    main_func()
