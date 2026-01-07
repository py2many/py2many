#!/usr/bin/env python3


def show():
    # Simple walrus operator
    if (n := len([1, 2, 3])) > 2:
        print(n)

    # Walrus in while loop
    i = 0
    while (x := i * 2) < 10:
        print(x)
        i += 1


if __name__ == "__main__":
    show()
