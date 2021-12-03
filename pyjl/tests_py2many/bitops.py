#!/usr/bin/env python3

from typing import List


def main():
    ands: List[bool] = []
    ors: List[bool] = []
    xors: List[bool] = []
    for a in [False, True]:
        for b in [False, True]:
            ands.append(a & b)
            ors.append(a | b)
            xors.append(a ^ b)
    assert ands == [False, False, False, True]
    assert ors == [False, True, True, True]
    assert xors == [False, True, True, False]
    print("OK")


if __name__ == "__main__":
    main()
