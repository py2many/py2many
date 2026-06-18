from std.testing import assert_true


struct Foo:
    fn __init__(out self: Foo):
        pass

    fn bar(self: Foo) -> Int:
        return self.baz()

    fn baz(self: Foo) -> Int:
        return 10


fn main() raises:
    var f = Foo()
    var b = f.bar()
    print(b)
    assert_true(b == 10)
