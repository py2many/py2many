import testing
from bar import bar1
from baz import baz1


fn main() raises:
    var x = bar1()
    var y = baz1()
    testing.assert_true(x == 0)
    testing.assert_true(y == "foo")
