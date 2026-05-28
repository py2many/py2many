from std.testing import assert_true


fn compare_assert(a: Int, b: Int) raises:
    assert_true(a == b)
    assert_true(not (0 == 1))


fn main() raises:
    assert_true(True)
    assert_true(not (False))
    compare_assert(1, 1)
    assert_true(True)
    assert_true(True)
    print("OK")
