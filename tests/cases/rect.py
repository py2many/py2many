"""This file implements a rectangle class """

from dataclasses import dataclass


@dataclass
class Rectangle:
    """Rectangle as a dataclass"""
    height: int
    length: int

    def is_square(self) -> bool:
        """Go likes this to be camel case"""
        return self.height == self.length


def show():
    r = Rectangle(height=1, length=1)
    assert r.is_square()

    r = Rectangle(height=1, length=2)
    assert not r.is_square()

    print(r.height)
    print(r.length)


if __name__ == "__main__":
    show()
