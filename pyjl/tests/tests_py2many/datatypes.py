#!/usr/bin/env python3

from adt import adt as sealed
from dataclasses import dataclass

@jl_dataclass # Remove when testing
@dataclass
class IntListNonEmpty:
    first: int
    rest: "IntList"


@sealed
class IntList:
    NONE: None
    REST: IntListNonEmpty
