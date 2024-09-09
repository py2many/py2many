import testing


struct Foo:
    fn __init__(inout self: Foo):
        pass

    fn bar(self: Foo) -> Int64:
        return self.baz()

    fn baz(self: Foo) -> Int64:
        return 10


fn main() raises:
    var f = Foo()
    var b = f.bar()
    print(b)
    testing.assert_true(b == 10)
