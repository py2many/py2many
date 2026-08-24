# This file implements a rectangle class


struct Rectangle:
    var height: Int
    var length: Int

    def __init__(out self, height: Int, length: Int):
        self.height = height
        self.length = length

    def is_square(self: Rectangle) raises -> Bool:
        return self.height == self.length


def show() raises:
    var r = Rectangle(height=1, length=1)
    assert r.is_square()
    r = Rectangle(height=1, length=2)
    assert not (r.is_square())
    print(r.height)
    print(r.length)


def main() raises:
    show()
