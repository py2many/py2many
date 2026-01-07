#!/usr/bin/env python3


def show():
    # Starred in list unpacking
    first, *middle, last = [1, 2, 3, 4, 5]
    print(first, last)


if __name__ == "__main__":
    show()
