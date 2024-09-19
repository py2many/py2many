import testing


fn compare_with_integer_variable() raises:
    var i: Int = 0
    var s: Int = 1
    if i:
        s = 2
    else:
        s = 3
    testing.assert_true(s == 3)


fn use_zero_for_comparison() raises:
    var i: Int = 0
    var s: Int = 1
    if 0:
        s = 2
    else:
        s = 3
    testing.assert_true(s == 3)


fn main() raises:
    compare_with_integer_variable()
    use_zero_for_comparison()
    print("OK")
