#!/usr/bin/env python3

from smtfe import Function, Variable, check_sat, get_value

a: bool = Variable("a")
b: bool = Variable("b")


@Function.wrap
def demorgan() -> bool:
    return (a & b) == (~ ((~ a) | (~ b)))


if __name__ == "__main__":
    assert demorgan
    check_sat()
    # get_value((a, b))

# z3 -smt2 demorgan.smt prints: a = True, b = True
