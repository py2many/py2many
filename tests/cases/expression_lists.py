# From PLR 6.15
# expression_list ::= expression ("," expression)* [","]
# starred_list ::= starred_item ("," starred_item)* [","]
# starred_expression ::= expression | (starred_item ",")* [starred_item]
# starred_item ::= assignment_expression | "*" or_expr

# conditional_expression ::= or_test ["if" or_test "else" expression]
# expression ::= conditional_expression | lambda_expr

# Examples taken from: https://www.python.org/dev/peps/pep-0448/

# Python's ast module converst all expression lists to tuples
from typing import Tuple


def expression_list():
    a = 1,2
    b = 7*8, 5-6
    c = 1, 2,
    assert a == (1, 2)
    assert b == (56, -1)
    assert c == (1,2)
    assert (a, 4) == ((1, 2), 4)
    assert isinstance(a, Tuple) # Check if type is correct


def starred_item():
    # Assignments
    a, *b, c = range(5)
    assert a == 0
    assert b == [1,2,3]
    assert c == 4
    # Dictionary
    assert {'x': 1, **{'y': 2}} == {'x': 1, 'y': 2}
    # Range
    assert [*range(4), 4] == [0,1,2,3,4]
    assert {*range(4), 4} == {0,1,2,3,4}


def starred_list():
    n = [1,2,3,4]
    assert [*n, 5, 6] == [1,2,3,4,5,6]
    assert (*[1], *[2], 3) == (1,2,3)
    assert (*[1,2,3], 4*1, 5) == (1,2,3,4, 5)


if __name__ == "__main__":
    expression_list()
    starred_item()
    starred_list()