#!/usr/bin/env python3

from py2many.smt import check_sat, get_value


def demorgan(a: bool, b: bool) -> bool:
    (a and b) == (not ((not a) or (not b)))


assert demorgan
check_sat()
get_value((a, b))
