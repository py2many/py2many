#!/usr/bin/env python3

from enum import IntEnum, IntFlag, Enum, auto


# IntEnum test
class Colors(IntEnum):
    RED = auto()
    GREEN = auto()
    BLUE = auto()


# IntFlag test
class Permissions(IntFlag):
    R = 1
    W = 2
    X = 16


# String enum test
class Status(str, Enum):
    ACTIVE = "active"
    INACTIVE = "inactive"
    PENDING = "pending"


def show():
    # Test IntEnum
    color = Colors.RED
    if color == Colors.RED:
        print("red")

    # Test IntFlag
    perm = Permissions.R | Permissions.W
    if perm & Permissions.R:
        print("has read")

    # Test StrEnum
    status = Status.ACTIVE
    if status == Status.ACTIVE:
        print("active")

    # Test in dict
    color_map = {Colors.RED: "red", Colors.GREEN: "green"}
    print(len(color_map))


if __name__ == "__main__":
    show()
