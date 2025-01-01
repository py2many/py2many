from typing import Callable

from adt import adt as sealed


@sealed
class OpType:
    add: Callable
    mul: Callable
