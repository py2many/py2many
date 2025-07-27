from py2many.smt import check_sat, default_value, get_value
from py2many.smt import pre as smt_pre

x: int = default_value(int)
y: int = default_value(int)
z: float = default_value(float)


def equation(x: int, y: int) -> bool:
    if smt_pre:
        assert x > 2
        assert y < 10
        assert x + 2 * y == 7
    True


def fequation(z: float) -> bool:
    if smt_pre:
        assert 9.8 + 2 * z == z + 9.11
    True


assert equation(x, y)
assert fequation(z)
check_sat()
get_value((x, y, z))
# z3 -smt2 equations.smt prints: x = 7, y = 0
