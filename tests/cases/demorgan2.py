#!/usr/bin/env python3

from py2many.smt import prove


def demorgan(a: bool, b: bool) -> bool:
    return (a and b) == (not ((not a) or (not b)))


def main():
    prove(demorgan)
    print("proven")


if __name__ == "__main__":
    main()
