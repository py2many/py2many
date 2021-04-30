#!/usr/bin/env python3

from ctypes import (
    c_int8,
    c_int16,
    c_int32,
    c_int64,
    c_uint8,
    c_uint16,
    c_uint32,
    c_uint64,
)


def foo():
    a = 10
    b = 20
    _c1 = a + b
    _c2 = a - b
    _c3 = a * b
    _c4 = a / b
    _c5 = -a
    d = 2.0
    _e1 = a + d
    _e2 = a - d
    _e3 = a * d
    _e4 = a / d
    _f = -3.0
    _g = -a


def add1(x: c_int8, y: c_int8):
    return x + y


def add2(x: c_int16, y: c_int16):
    return x + y


def add3(x: c_int32, y: c_int32):
    return x + y


def add4(x: c_int64, y: c_int64):
    return x + y


def add5(x: c_uint8, y: c_uint8):
    return x + y


def add6(x: c_uint16, y: c_uint16):
    return x + y


def add7(x: c_uint32, y: c_uint32):
    return x + y


def add8(x: c_uint64, y: c_uint64):
    return x + y


def add9(x: c_int8, y: c_uint16):
    return x + y


def sub(x: c_int8, y: c_int8):
    return x - y


def mul(x: c_int8, y: c_int8):
    return x * y


def fadd1(x: c_int8, y: float):
    return x + y


def show():
    rv = fadd1(6, 6.0)
    assert rv == 12
    print("OK")


if __name__ == "__main__":
    foo()
    show()
