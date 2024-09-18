import testing


fn foo() raises:
    var a = 10
    var b = a
    testing.assert_true(b == 10)
    print(b)


fn main() raises:
    foo()
