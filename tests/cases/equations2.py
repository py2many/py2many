#!/usr/bin/env python3

from py2many.smt import check


def equation(x: int, y: int) -> bool:
    return x > 2 and y < 10 and x + 2 * y == 7


def fequation(z: float) -> bool:
    # 7 * z == 1; the solution 1/7 is written as the 6-decimal literal 0.142857
    # so it prints identically under Python's str() and Lean's Float.toString
    # (both emit "0.142857"), needing no float-formatting shim.
    diff = 7.0 * z - 1.0
    return -0.001 < diff and diff < 0.001


def main():
    x = 7
    y = 0
    z = 0.142857
    check(equation(x, y))
    check(fequation(z))
    print(x)
    print(y)
    print(z)


if __name__ == "__main__":
    main()
