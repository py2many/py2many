#!/usr/bin/env python3


def generator1():
    yield 1
    yield 2
    yield 3


def generator2():
    yield 0
    yield from generator1()
    yield 4


def show():
    gen = generator2()
    for val in gen:
        print(val)


if __name__ == "__main__":
    show()
