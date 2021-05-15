#!/usr/bin/env python3

from ctypes import c_int8


def sum_as_string(a: c_int8, b: c_int8) -> str:
    return str(a + b)


def add_key(d: dict) -> None:
    d[1] = 2
    return
