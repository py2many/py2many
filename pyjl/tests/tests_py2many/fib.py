#!/usr/bin/env python3


def fib(i: int) -> int:
    if i == 0 or i == 1:
        return 1
    return fib(i - 1) + fib(i - 2)


if __name__ == "__main__":
    print(fib(5))
