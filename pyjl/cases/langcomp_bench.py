#!/usr/bin/env python3

from typing import List


def test_python(iterations: int):
    iteration = 0
    total = float(0.0)
    array_length = 1000
    array: List[int] = [i for i in range(array_length)]
    print("iterations", iterations)
    while iteration < iterations:
        innerloop = 0
        while innerloop < 100:
            total += array[(iteration + innerloop) % array_length]
            innerloop += 1
        iteration += 1
    if total == 15150:
        print("OK")
    del array


if __name__ == "__main__":
    test_python(3)
