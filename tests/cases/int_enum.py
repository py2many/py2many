from enum import IntEnum, IntFlag, auto


class Colors(IntEnum):
    RED = auto()
    GREEN = auto()
    BLUE = auto()


class Permissions(IntFlag):
    R = 1
    W = 2
    X = 16
