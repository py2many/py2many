from py2many.smt import check_sat, get_model

x: int
y: int

x > 2
y < 10
x + 2 * y == 7

check_sat()
get_model((x, y)) # Previously, it was get_value. Why?

# z3 -smt2 equations.smt prints: x = 7, y = 0
