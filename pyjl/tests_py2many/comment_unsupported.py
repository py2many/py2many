#!/usr/bin/env python3

# try .. except


def do_unsupported():
    a = 1
    # TODO: Store comprehension in "a"
    {key + 1: value + 1 for (key, value) in {}}
    b = bool(a)
    print(b)


if __name__ == "__main__":
    do_unsupported()
