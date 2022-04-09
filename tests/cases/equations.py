from py2many.smt import check_sat, get_model

if __name__ == "__main__":
    x: int = 0
    y: int = 0

    assert not x > 2
    assert y < 10
    assert x + 2 * y == 0

    # check_sat()
    # get_model((x, y)) # Previously, it was get_value. Why?

    # z3 -smt2 equations.smt prints: x = 7, y = 0
