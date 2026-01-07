#!/usr/bin/env python3


def show():
    # Generator expression
    gen = (x * x for x in range(5))
    for val in gen:
        print(val)


if __name__ == "__main__":
    show()
