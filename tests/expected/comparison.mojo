import testing


fn compare_with_integer_variable() raises:
    var i: Int64 = 0
    var s: Int64 = 1
    if i:
        var s = 2
    else:
        var s = 3
    testing.assert_true(s == 3)


fn use_zero_for_comparison() raises:
    var i: Int64 = 0
    var s: Int64 = 1
    if 0:
        var s = 2
    else:
        var s = 3
    testing.assert_true(s == 3)


fn main() raises:
    compare_with_integer_variable()
    use_zero_for_comparison()
    print("OK")
