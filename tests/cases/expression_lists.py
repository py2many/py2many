# Examples taken from:
# - https://www.python.org/dev/peps/pep-0448/
# - https://www.python.org/dev/peps/pep-3132/

# Python's ast module already converts all expression lists to tuples

from typing import Tuple


def expression_list():
    a = 1, 2
    b = 7 * 8, 5 - 6
    c = 1, 2
    assert a == (1, 2)
    assert b == (56, -1)
    assert c == (1, 2)
    assert (a, 4) == ((1, 2), 4)
    assert isinstance(a, Tuple)


def starred_item():
    # Assignments
    a, *b, c = range(6)
    assert a == 0
    assert b == [1, 2, 3, 4]
    assert c == 5
    # Dictionary
    assert {"x": 1, **{"y": 2}} == {"x": 1, "y": 2}
    # Range
    assert [*range(4), 4] == [0, 1, 2, 3, 4]
    assert {*range(4), 4} == {0, 1, 2, 3, 4}


def starred_list():
    n = [1, 2, 3, 4]
    assert [*n, 5, 6] == [1, 2, 3, 4, 5, 6]
    assert (*[1], *[2], 3) == (1, 2, 3)
    assert (*[1, 2, 3], 4 * 1, 5) == (1, 2, 3, 4, 5)


if __name__ == "__main__":
    expression_list()
    starred_item()
    starred_list()
