from std.testing import assert_true


fn foo() raises:
    var a = 10
    var b = a
    assert_true(b == 10)
    print(b)


fn main() raises:
    foo()
