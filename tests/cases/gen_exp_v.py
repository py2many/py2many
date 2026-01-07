#!/usr/bin/env python3


def show():
    # Generator expression
    gen = (x * x for x in range(5))
    for val in gen:
        print(val)

    # Generator expression with condition
    evens = (x for x in range(10) if x % 2 == 0)
    count = sum(evens)
    print(count)

    # List comprehension (should work similarly)
    squares = [x * x for x in range(5)]
    print(len(squares))


if __name__ == "__main__":
    show()
