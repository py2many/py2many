#!/usr/bin/env python3


def compare_assert(a: int, b: int):
    assert a == b
    assert not (0 == 1)


if __name__ == "__main__":
    compare_assert(1, 1)
