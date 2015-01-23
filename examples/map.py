#!/usr/bin/env python
def map(values, fun):
    results = []
    for v in values:
        results.append(fun(v))
    return results


def square(n):
    return n * n


if __name__ == "__main__":
    values = [1, 2, 3, 4, 5]
    results = map(values, square)
    for v in results:
        print(v)
