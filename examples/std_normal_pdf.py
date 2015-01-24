#!/usr/bin/env python
import math

def pdf(x, mean, std_dev):
    term1 = 1.0 / ((2 * math.pi) ** 0.5)
    term2 = math.e ** (-1.0 * (x-mean) ** 2.0 / 2.0 * (std_dev ** 2.0))

    return term1 * term2


if __name__ == "__main__":
    a = pdf(1, 0, 1)
    print(str(a) + " should be close to " + str(0.24197072451914337))
