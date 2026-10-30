#!/usr/bin/env python3
"""Tiny arithmetic expression parser and evaluator.

Written in the match-as-expression dialect: digit decoding, operator
classification, operator application and operator precedence are all
match expressions, e.g.::

    kind = match code:
        43: PLUS
        45: MINUS
        _: -1

Nested matches and parenthesized matches are supported too::

    return (
        match precedence(op1):
            2: match precedence(op2):
                2: 22
                _: 20
            _: 0
    )

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


def op_kind(code: int) -> int:
    return match code:
        43: PLUS
        45: MINUS
        42: STAR
        47: SLASH
        40: LPAREN
        41: RPAREN
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


def sign_kind(code: int) -> int:
    return (
        match (match code:
            43: 1
            45: 2
            _: 0):
        1: 10
        2: 20
        _: 0
    )


def prec_pair(op1: int, op2: int) -> int:
    return (
        match precedence(op1):
            2: match precedence(op2):
                2: 22
                1: 21
                _: 20
            1: match precedence(op2):
                2: 12
                1: 11
                _: 10
            _: 0
    )


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
    # Pre-declared: first assigned inside nested loops, where the
    # declaration extractor would otherwise miss them.
    top = 0
    left = 0
    right = 0
    nxt = 0
    while i < n:
        code = codes[i]
        digit = digit_value(code)
        if digit >= 0:
            value = 0
            while i < n:
                digit = digit_value(codes[i])
                if digit < 0:
                    break
                value = value * 10 + digit
                i = i + 1
            if nv < len(values):
                values[nv] = value
            else:
                values.append(value)
            nv = nv + 1
            continue
        kind = op_kind(code)
        nxt = i + 1
        if kind == SLASH:
            if nxt < n:
                if op_kind(codes[nxt]) == SLASH:
                    i = nxt
        if kind == LPAREN:
            if no < len(ops):
                ops[no] = kind
            else:
                ops.append(kind)
            no = no + 1
        elif kind == RPAREN:
            while no > 0:
                top = ops[no - 1]
                if top == LPAREN:
                    break
                right = values[nv - 1]
                left = values[nv - 2]
                nv = nv - 2
                values[nv] = apply_op(top, left, right)
                nv = nv + 1
                no = no - 1
            no = no - 1
        else:
            while no > 0:
                top = ops[no - 1]
                if top == LPAREN:
                    break
                if precedence(top) < precedence(kind):
                    break
                right = values[nv - 1]
                left = values[nv - 2]
                nv = nv - 2
                values[nv] = apply_op(top, left, right)
                nv = nv + 1
                no = no - 1
            if no < len(ops):
                ops[no] = kind
            else:
                ops.append(kind)
            no = no + 1
        i = i + 1
    while no > 0:
        top = ops[no - 1]
        right = values[nv - 1]
        left = values[nv - 2]
        nv = nv - 2
        values[nv] = apply_op(top, left, right)
        nv = nv + 1
        no = no - 1
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
    print(sign_kind(43))
    print(sign_kind(45))
    print(sign_kind(48))
    print(prec_pair(3, 4))
    print(prec_pair(3, 1))
    print(prec_pair(1, 4))
    print(prec_pair(1, 1))
    print(prec_pair(5, 1))
