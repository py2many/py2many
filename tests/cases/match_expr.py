#!/usr/bin/env python3
"""Tiny arithmetic expression parser and evaluator.

Written in the match-as-expression dialect: digit decoding, operator
application and operator precedence are all match expressions, e.g.::

    kind = match code:
        43: PLUS
        45: MINUS
        _: -1

The evaluator itself dispatches on the raw character code with a large
match, as in a classic functional-language lexer. A ``/`` following
another ``/`` is the second half of ``//``, not division: a nested
match tells the two apart::

    kind = match code:
        47: match prev:
            4: -2
            _: SLASH
        40: LPAREN
        _: -1

The parser consumes a list of character codes (``[50, 43, 51]`` is
``"2+3"``) with an iterative shunting-yard evaluator, so the same
source transpiles to both Rust and CPython.
"""

from typing import List

PLUS = 1
MINUS = 2
STAR = 3
SLASH = 4
LPAREN = 5
RPAREN = 6


def digit_value(code: int) -> int:
    return match code:
        48: 0
        49: 1
        50: 2
        51: 3
        52: 4
        53: 5
        54: 6
        55: 7
        56: 8
        57: 9
        _: -1


def apply_op(op: int, left: int, right: int) -> int:
    return match op:
        1: left + right
        2: left - right
        3: left * right
        4: left // right
        _: 0


def precedence(op: int) -> int:
    return match op:
        3: 2
        4: 2
        1: 1
        2: 1
        _: 0


# Note: evaluate has no `-> int` annotation. Returning a list element
# with a declared `-> int` trips a pre-existing inference bug
# (declared `int` merged with inferred `i32` into `Union[int,i32]`).
# The return type is inferred as i32 instead.
def evaluate(codes: List[int]):
    values: List[int] = []
    ops: List[int] = []
    nv = 0
    no = 0
    i = 0
    n = len(codes)
    prev = 0
    while i < n:
        code = codes[i]
        # Operator classification is a large match on the raw character
        # code, as in a classic functional-language lexer. The nested
        # match spots the second `/` of `//` (marked -2 and skipped
        # below) so it isn't treated as division.
        kind = match code:
            43: PLUS
            45: MINUS
            42: STAR
            47: match prev:
                4: -2
                _: SLASH
            40: LPAREN
            41: RPAREN
            _: -1
        digit = digit_value(code)
        if digit >= 0:
            value = 0
            while i < n:
                digit = digit_value(codes[i])
                if digit < 0:
                    break
                value = value * 10 + digit
                i += 1
            if nv < len(values):
                values[nv] = value
            else:
                values.append(value)
            nv += 1
            prev = -1
            continue
        if kind == -2:
            i += 1
            continue
        if kind == LPAREN:
            if no < len(ops):
                ops[no] = kind
            else:
                ops.append(kind)
            no += 1
        elif kind == RPAREN:
            while no > 0:
                if ops[no - 1] == LPAREN:
                    break
                nv -= 2
                values[nv] = apply_op(ops[no - 1], values[nv], values[nv + 1])
                nv += 1
                no -= 1
            no -= 1
        else:
            while no > 0:
                if ops[no - 1] == LPAREN:
                    break
                if precedence(ops[no - 1]) < precedence(kind):
                    break
                nv -= 2
                values[nv] = apply_op(ops[no - 1], values[nv], values[nv + 1])
                nv += 1
                no -= 1
            if no < len(ops):
                ops[no] = kind
            else:
                ops.append(kind)
            no += 1
        prev = kind
        i += 1
    while no > 0:
        nv -= 2
        values[nv] = apply_op(ops[no - 1], values[nv], values[nv + 1])
        nv += 1
        no -= 1
    return values[0]


if __name__ == "__main__":
    # "2+3*4"
    print(evaluate([50, 43, 51, 42, 52]))
    # "(2+3)*4"
    print(evaluate([40, 50, 43, 51, 41, 42, 52]))
    # "10-8//2"
    print(evaluate([49, 48, 45, 56, 47, 47, 50]))
    # "7*8+9"
    print(evaluate([55, 42, 56, 43, 57]))
    # "((2+3)*4)-6"
    print(evaluate([40, 40, 50, 43, 51, 41, 42, 52, 41, 45, 54]))
