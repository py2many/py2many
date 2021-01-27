from dataclasses import dataclass


@dataclass
class Rectangle:
    height: int
    length: int

    def is_square(self) -> bool:
        return height == length
