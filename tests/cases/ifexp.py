#!/usr/bin/env python3


def show():
    # ifexp
    a = 1
    b = 2 if a in [2, 3] else 3
    print(b)


if __name__ == "__main__":
    show()
