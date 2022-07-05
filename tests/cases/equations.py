#!/usr/bin/env python3

from smtfe import Variable, check_sat, get_value

x: int = Variable("x")
y: int = Variable("y")

x > 2
y < 10
x + 2 * y == 7

if __name__ == "__main__":
    check_sat()
    get_value((x, y))

# z3 -smt2 equations.smt prints: x = 7, y = 0
