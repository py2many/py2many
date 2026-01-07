#!/usr/bin/env python3

global_var = 10


def test_global():
    global global_var
    global_var = 20
    print(global_var)


def show():
    test_global()


if __name__ == "__main__":
    show()
