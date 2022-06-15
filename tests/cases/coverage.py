# Generic Test that covers many features

from typing import List


def inline_pass():
    pass


def inline_ellipsis():
    ...


def indexing():
    sum = 0
    a: List[int] = []
    for i in range(10):
        a.append(i)
        sum += a[i]
    return sum


def infer_bool(code: int):
    return code in [1, 2, 4]


def show():
    # assign
    a1 = 10

    # multi-assign
    b1 = b2 = 15
    assert b1 == 15
    assert b2 == 15
    b9 = 2
    b10 = 2
    assert b9 == b10

    # annotated assign
    a2: float = 2.1
    assert a2 == 2.1

    # for loop
    # Result array
    res = []
    for i in range(0, 10):
        res.append(i)
    for i in range(0, 10, 2):
        res.append(i)
    for i in range(1, 10):
        res.append(i)
    assert res == [
        0,
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        9,
        0,
        2,
        4,
        6,
        8,
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        9,
    ]

    # unary op
    a3 = -a1
    assert a3 == -10

    # binary op
    a4 = a3 + a1
    assert a4 == 0

    # ternary op
    t1 = 10 if a1 > 5 else 5
    assert t1 == 10

    # Indexing
    sum1 = indexing()
    assert sum1 == 45

    # lists
    a5 = [1, 2, 3]
    print(len(a5))
    a9 = ["a", "b", "c", "d"]
    assert len(a9) == 4
    assert a9 == ["a", "b", "c", "d"]

    # Sets
    a6 = {1, 2, 3, 4}
    i = iter(a6)  # Might give problems in certain transpilers
    assert len(a6) == 4
    assert next(i, None) == 1
    assert next(i, None) == 2
    assert next(i, None) == 3
    assert next(i, None) == 4
    assert next(i, None) == None

    # Dicts
    a7 = {"a": 1, "b": 2}
    assert len(a7) == 2
    assert a7["a"] == 1
    assert a7["b"] == 2

    # Boolean tests
    a8 = True
    a10 = False
    assert a10 == True
    assert a9 == False
    if True:
        a1 += 1
    assert a1 == 11
    assert bool(1)

    # Check element inclusion
    assert infer_bool(1)

    # Assert test
    assert 1 != 2 != 3

    # print()
    if a8:
        print("true")
    elif a4 > 0:
        print("never get here")
    if a1 == 11:
        print("false")
    else:
        print("true")
    if 1 != None:
        print("World is sane")
    print(True)
    if True:
        print("true")

    # Testing pass
    inline_pass()

    # Testing string with tab (tab is equal to four spaces)
    s = "1\
    2"
    assert s == "1    2"

    # Escape quotes
    _escape_quotes = """ foo "bar" baz """
    assert "bbc" in "aaabbccc"

    # Test assignment
    (_c1, _, _c2) = (1, 2, 3)
    [_c3, _, _c4] = [1, 2, 3]
    assert _c1 == 1
    assert _c2 == 3
    assert _c3 == 1
    assert _c4 == 3


if __name__ == "__main__":
    show()
