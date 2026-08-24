from bar import bar1
from baz import baz1


def main() raises:
    var x = bar1()
    var y = baz1()
    assert x == 0
    assert y == "foo"
