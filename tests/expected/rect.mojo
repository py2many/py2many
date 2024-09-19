import testing

# This file implements a rectangle class


@value
struct Rectangle:
    var height: Int
    var length: Int

    fn is_square(self: Rectangle) -> Bool:
        return self.height == self.length


fn show() raises:
    var r = Rectangle(height=1, length=1)
    testing.assert_true(r.is_square())
    r = Rectangle(height=1, length=2)
    testing.assert_true(not (r.is_square()))
    print(r.height)
    print(r.length)


fn main() raises:
    show()
