#!/usr/bin/env python3

from py2many.smt import check_sat


def demorgan(a: bool, b: bool) -> bool:
    (a and b) == (not ((not a) or (not b)))


a: Bool
b: Bool

assert not demorgan(a, b)
check_sat()
