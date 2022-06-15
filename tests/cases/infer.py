#!/usr/bin/env python3


def foo():
    a = 10
    # infer that b is an int
    b = a
    assert b == 10


def fibonacci(n):
    if n == 0:
        return 0
    elif n == 1:
        return 1
    else:
        return fibonacci(n - 2) + fibonacci(n - 1)


def mul_list():
    a: list = []
    for i in range(0, 5):
        a.append(i)
    return 2 * a


def combinations(array):
    result = []
    for x in array:
        for y in array:
            result.append((x, y))
    return result


def mul_recvd_list(a: list):
    for i in range(0, len(a)):
        a.append(i)
    return 2 * a


# Runtime information
def plus_test(x, y):
    return x + y


# Compile time information
def plus_test(x: str, y: str):
    return x + y


if __name__ == "__main__":
    foo()

    # Test inference with functions
    # 1
    assert fibonacci(10) == 55
    assert fibonacci(3) * "test" == "testtest"
    a = []
    a_mul = mul_recvd_list(a)
    assert a_mul == []

    # 2
    x = "ss"
    y = "zz"
    res = plus_test(x, y)
    assert res == "sszz"

    print("OK")
