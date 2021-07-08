from bar import bar1
from baz import baz1

if __name__ == "__main__":
    x = bar1()
    y = baz1()
    assert x == 0
    assert y == "foo"
