#!/usr/bin/env python3


def show():
    # Simple dict comprehension
    squares = {x: x * x for x in range(5)}
    print(len(squares))

    # Dict comprehension with condition
    evens = {x: x * 2 for x in range(10) if x % 2 == 0}
    print(len(evens))


if __name__ == "__main__":
    show()
