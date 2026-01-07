#!/usr/bin/env python3

from typing import Callable


def show():
    # Simple lambda
    myfunc: Callable[[int, int], int] = lambda x, y: x + y
    print(myfunc(1, 2))

    # Lambda with multiple statements (not supported in V, but should handle gracefully)
    # lambda2 = lambda x: (y := x + 1, y * 2)

    # Lambda in list comprehension
    result = [lambda x: x * i for i in range(3)]
    print(len(result))


if __name__ == "__main__":
    show()
