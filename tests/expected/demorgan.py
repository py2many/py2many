#!/usr/bin/env python3

from py2many.smt import check_sat


def demorgan(a: bool, b: bool) -> bool:
    return (a and b) == (not ((not a) or (not b)))


assert demorgan(True, True)
assert demorgan(True, False)
assert demorgan(False, True)
assert demorgan(False, False)
# assert not demorgan # Should fail if uncommented
# check_sat()
print("OK")
