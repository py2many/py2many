from dataclasses import dataclass


@dataclass
class Rectangle:
    height: int
    length: int

    def is_square(self) -> bool:
        return self.height == self.length


def show():
	r = Rectangle(height=1, length=1)
	assert r.is_square()

	r = Rectangle(height=1, length=2)
	assert not r.is_square()

	# Avoiding print with object attributes due to
	# https://github.com/adsharma/py2many/issues/64
	h = r.height
	l = r.length
	print(h)
	print(l)


if __name__ == "__main__":
	show()
