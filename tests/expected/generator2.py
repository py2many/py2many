from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys


def simple_generator():
    yield 1
    yield 2
    yield 3


def generator_with_type():
    x: int = 0
    while x < 5:
        yield x
        x += 1


def generator_with_args(a: int, b: int):
    for i in range(a, b):
        yield (i * 2)


def generator_with_yield_from():

    def inner():
        yield 1
        yield 2

    yield from inner()
    yield 3


def generator_with_condition():
    for i in range(10):
        if i % 2 == 0:
            yield i


def generator_calls():
    gen1 = simple_generator()
    gen2 = generator_with_args(1, 5)


def consume_generators():
    for val in simple_generator():
        print(val)
    for val in generator_with_type():
        print(val)
    for val in generator_with_args(1, 5):
        print(val)
    for val in generator_with_yield_from():
        print(val)
    for val in generator_with_condition():
        print(val)


if __name__ == "__main__":
    generator_calls()
    consume_generators()
