from bar import bar1
from baz import baz1
from testing import assert_true


fn main() raises:
    var x = bar1()
    var y = baz1()
    assert_true(x == 0)
    assert_true(y == "foo")
