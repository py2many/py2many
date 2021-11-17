#!/usr/bin/env python3

from adt import adt as sealed
from dataclasses import dataclass


@dataclass
class IntListNonEmpty:
    first: int
    rest: "IntList"


@sealed
class IntList:
    NONE: None
    REST: IntListNonEmpty
