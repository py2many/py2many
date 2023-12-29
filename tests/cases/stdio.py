#!/usr/bin/env python3

import sys

# from sys import stdout # FIXME: sys is an ignored export, so this does not work properly.


def main():
    sys.stdout.write("foobar\n")
    # stdout.flush()


if __name__ == "__main__":
    main()
