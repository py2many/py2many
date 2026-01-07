#!/usr/bin/env python3


def simple_generator():
    """Simple generator with yield"""
    yield 1
    yield 2
    yield 3


def show():
    # Test simple generator
    gen = simple_generator()
    for val in gen:
        print(val)


if __name__ == "__main__":
    show()
