struct Foo:
    def __init__(out self: Foo):
        pass

    def bar(self: Foo) raises -> Int:
        return self.baz()

    def baz(self: Foo) raises -> Int:
        return 10


def main() raises:
    var f = Foo()
    var b = f.bar()
    print(b)
    assert b == 10
