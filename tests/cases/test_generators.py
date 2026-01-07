"""Test cases for generator functions and yield statements"""


def simple_generator():
    """Simple generator yielding values"""
    yield 1
    yield 2
    yield 3


def generator_with_type():
    """Generator with type annotation"""
    x: int = 0
    while x < 5:
        yield x
        x += 1


def generator_with_args(a: int, b: int):
    """Generator with parameters"""
    for i in range(a, b):
        yield i * 2


def generator_with_yield_from():
    """Generator using yield from"""

    def inner():
        yield 1
        yield 2

    yield from inner()
    yield 3


def generator_with_condition():
    """Generator with conditional yield"""
    for i in range(10):
        if i % 2 == 0:
            yield i


# Test calls
def test_generator_calls():
    """Test calling generator functions"""
    # These should be spawned with channels
    gen1 = simple_generator()
    gen2 = generator_with_args(1, 5)

    # Iteration would need channel handling
    # for val in gen1: print(val)
