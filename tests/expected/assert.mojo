def compare_assert(a: Int, b: Int) raises:
    assert a == b
    assert not (0 == 1)


def main() raises:
    assert True
    assert not (False)
    compare_assert(1, 1)
    assert True
    assert True
    print("OK")
