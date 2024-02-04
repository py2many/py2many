class Foo:

    def bar(self):
        return self.baz()

    def baz(self) -> int:
        return 10


if __name__ == "__main__":
    f = Foo()
    b = f.bar()
    print(b)
    assert b == 10
