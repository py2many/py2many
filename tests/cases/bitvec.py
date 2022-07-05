#!/usr/bin/env python3
from __future__ import annotations
from smtfe import BitVec, check_sat, get_value

myu32: BitVec[32] = BitVec("myu32", 32)

myu32 == 0x0000000a

if __name__ == "__main__":
    check_sat()
    get_value((myu32, ))

# z3 -smt2 bitvec.smt prints: myu32 #x0000000a
