import testing


fn compare_assert(a: Int, b: Int) raises:
    testing.assert_true(a == b)
    testing.assert_true(not (0 == 1))


fn main() raises:
    testing.assert_true(True)
    testing.assert_true(not (False))
    compare_assert(1, 1)
    testing.assert_true(True)
    testing.assert_true(True)
    print("OK")
