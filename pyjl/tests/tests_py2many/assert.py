#!/usr/bin/env python3


def compare_assert(a: int, b: int):
    assert a == b
    assert not (0 == 1)


if __name__ == "__main__":
    assert True
    assert not False
    compare_assert(1, 1)
    # assert not None
    # assert not 0
    # with message
    assert True, 1
    assert True, "message"
    print("OK")
