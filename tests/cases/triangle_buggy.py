from adt import adt as sealed

from py2many.smt import check_sat, default_value, get_model
from py2many.smt import pre as smt_pre


@sealed
class TriangleType:
    EQUILATERAL: int
    ISOSCELES: int
    RIGHT: int
    ACUTE: int
    OBTUSE: int
    ILLEGAL: int


# Create default values for SMT solver
a: int = default_value(int)
b: int = default_value(int)
c: int = default_value(int)


def classify_triangle_correct(a: int, b: int, c: int) -> TriangleType:
    """Classify triangle based on side lengths"""

    # Classify the triangle
    if a == b and b == c:
        return TriangleType.EQUILATERAL
    elif a == b or b == c or a == c:
        return TriangleType.ISOSCELES
    else:
        # Classify by angle using Pythagorean theorem
        # Check all cases where each side could be the largest
        #
        # Using x, y, z = sorted([a, b, c]) would be more readable, but harder to translate to SMT
        # So we manually check each case assuming a >= b >= c
        if a >= b and a >= c:
            # a is the largest side
            if a * a == b * b + c * c:
                return TriangleType.RIGHT
            elif a * a < b * b + c * c:
                return TriangleType.ACUTE
            else:
                return TriangleType.OBTUSE
        elif b >= a and b >= c:
            # b is the largest side
            if b * b == a * a + c * c:
                return TriangleType.RIGHT
            elif b * b < a * a + c * c:
                return TriangleType.ACUTE
            else:
                return TriangleType.OBTUSE
        else:
            # c is the largest side
            if c * c == a * a + b * b:
                return TriangleType.RIGHT
            elif c * c < a * a + b * b:
                return TriangleType.ACUTE
            else:
                return TriangleType.OBTUSE


def classify_triangle(a: int, b: int, c: int) -> TriangleType:
    """Classify triangle based on side lengths - buggy implementation matching Racket code"""
    # Pre-condition: all sides must be positive and satisfy triangle inequality
    if smt_pre:
        assert a > 0
        assert b > 0
        assert c > 0
        assert a < (b + c)

    if a >= b and b >= c:
        # Check for equal sides
        if a == c or b == c:
            if a == b and a == c:
                return TriangleType.EQUILATERAL
            else:
                return TriangleType.ISOSCELES
        else:
            # Check by angle using Pythagorean theorem
            # BUG: Not sorting sides, assuming a is largest (from a >= b >= c)
            if a * a != b * b + c * c:
                if a * a < b * b + c * c:
                    return TriangleType.ACUTE
                else:
                    return TriangleType.OBTUSE
            else:
                return TriangleType.RIGHT
    else:
        return TriangleType.ILLEGAL


# Test with SMT solver
assert not classify_triangle_correct(a, b, c) == classify_triangle(a, b, c)
check_sat()
get_model()
