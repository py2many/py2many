#!/usr/bin/env python3

from typing import Callable

# from typing import Protocol
#
# class LambdaFunction(Protocol):
#    def __call__(self, x: int, y: int) -> int:
#        ...


def show():
    myfunc = lambda x, y: x + y
    return myfunc(1, 2)


if __name__ == "__main__":
    assert show() == 3
