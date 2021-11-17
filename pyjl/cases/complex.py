#!/usr/bin/env python3


def complex_test():
    c1 = 2 + 3j
    c2 = 4 + 5j
    c3 = c1 + c2
    assert c3 == 6 + 8j
    c4 = c1 + 3
    assert c4 == 5 + 3j
    c5 = c1 + 4j
    assert c5 == 2 + 7j
    c6 = c3 - 2.3
    assert c6 == 3.7 + 8j


if __name__ == "__main__":
    complex_test()
    print("OK")
