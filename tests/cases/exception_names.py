#!/usr/bin/env python3


def show():
    try:
        3 / 0
    except ZeroDivisionError:
        print("ZeroDivisionError")


if __name__ == "__main__":
    show()
