#!/usr/bin/env python3

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
    if args.n == 0:
        args.n = 5
    print(fib(args.n))
