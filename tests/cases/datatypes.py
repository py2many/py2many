#!/usr/bin/env python3

from dataclasses import dataclass

from adt import adt as sealed


@dataclass
class IntListNonEmpty:
    first: int
    rest: "IntList"


@sealed
class IntList:
    NONE: None
    REST: IntListNonEmpty
