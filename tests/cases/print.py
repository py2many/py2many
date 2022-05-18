#!/usr/bin/env python3


import sys


def show():
    print("b")
    print(2, "b")
    a: float = 2.1
    print(a)
    b = 2.1
    print(b)
    c = True
    print(c)
    name = "test"
    val = True
    print(
        "%s_vtables_dispatch_ = %d" % (name, val),
        file=sys.stdout,
    )


if __name__ == "__main__":
    show()
