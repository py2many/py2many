from std.testing import assert_true

# This file implements a rectangle class


@fieldwise_init
struct Rectangle(Copyable, Movable):
    var height: Int
    var length: Int

    fn is_square(self: Rectangle) -> Bool:
        return self.height == self.length


fn show() raises:
    var r = Rectangle(height=1, length=1)
    assert_true(r.is_square())
    r = Rectangle(height=1, length=2)
    assert_true(not (r.is_square()))
    print(r.height)
    print(r.length)


fn main() raises:
    show()
