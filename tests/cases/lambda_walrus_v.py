#!/usr/bin/env python3


def show():
    # Lambda with walrus (Python 3.8+)
    # This is a complex case that might not work perfectly
    # but we should handle it gracefully

    # Simple case
    f = lambda x: x + 1
    print(f(5))

    # Lambda in map
    nums = [1, 2, 3]
    result = list(map(lambda x: x * 2, nums))
    print(len(result))


if __name__ == "__main__":
    show()
