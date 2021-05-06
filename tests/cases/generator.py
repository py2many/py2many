#!/usr/bin/env python3


def gen():
    yield 4
    yield 5
    return "foo"


def main():
    assert list(gen()) == [4, 5]


if __name__ == "__main__":
    main()
