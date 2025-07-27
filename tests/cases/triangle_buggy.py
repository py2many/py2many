from adt import adt as sealed

from py2many.smt import check_sat, default_value
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
        # Sort sides so that a is the largest
        x, y, z = sorted([a, b, c], reverse=True)
        if x * x == y * y + z * z:
            return TriangleType.RIGHT
        elif x * x < y * y + z * z:
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
assert classify_triangle_correct(a, b, c) == classify_triangle(a, b, c)
check_sat()
