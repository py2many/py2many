def foo() raises:
    var a = 10
    var b = a
    assert b == 10
    print(b)


def main() raises:
    foo()
