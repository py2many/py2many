def compare_with_integer_variable():
    i: int = 0
    s: int = 1
    if i:
        s = 2
    else:
        s = 3

    assert s == 3


def use_zero_for_comparison():
    i: int = 0
    s: int = 1
    if 0:
        s = 2
    else:
        s = 3

    assert s == 3


if __name__ == "__main__":
    compare_with_integer_variable()
    use_zero_for_comparison()
    print("OK")
