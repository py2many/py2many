#!/usr/bin/env python3
"""Tiny arithmetic expression parser and evaluator.

Written in the match-as-expression dialect, shaped like a classic
functional-language front end: a ``tokenize`` lexer turns character codes
into token kinds with a large match, and ``evaluate`` parses and evaluates
the token stream with an iterative shunting-yard evaluator, e.g.::

    kind = match code:
        48: NUM
        43: PLUS
        47: match prev:
            4: SKIP
            _: SLASH
        _: -1

A ``/`` following another ``/`` is the second half of ``//``, not
division: the nested match spots it and marks it ``SKIP``.

Per the static-python rules, fallible functions return ``Result[V, E]``
instead of raising: applying ``//`` to zero yields ``Err``, which the
caller prints with ``unwrap_or``::

    return match op:
        4: Ok(left // right) if right != 0 else Error("Division by zero")
        _: Ok(0)

The parser consumes a list of character codes (``[50, 43, 51]`` is
``"2+3"``), so the same source transpiles to Rust, V and CPython (whose
``match`` statement the python backend emits directly).
"""

from typing import List

from py2many.result import Error, Ok, Result

NUM = 0
PLUS = 1
MINUS = 2
STAR = 3
SLASH = 4
LPAREN = 5
RPAREN = 6
SKIP = -2


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


def apply_op(op: int, left: int, right: int) -> Result[int, str]:
    return match op:
        1: Ok(left + right)
        2: Ok(left - right)
        3: Ok(left * right)
        4: Ok(left // right) if right != 0 else Error("Division by zero")
        _: Ok(0)


def precedence(op: int) -> int:
    return match op:
        3: 2
        4: 2
        1: 1
        2: 1
        _: 0


def tokenize(codes: List[int]) -> List[int]:
    # Lex character codes into one token kind per character, as in a
    # classic functional-language lexer. SKIP marks the second `/` of
    # `//`, which the parser ignores.
    kinds: List[int] = []
    i = 0
    n = len(codes)
    prev = 0
    while i < n:
        code = codes[i]
        kind = match code:
            48: NUM
            49: NUM
            50: NUM
            51: NUM
            52: NUM
            53: NUM
            54: NUM
            55: NUM
            56: NUM
            57: NUM
            43: PLUS
            45: MINUS
            42: STAR
            47: match prev:
                4: SKIP
                _: SLASH
            40: LPAREN
            41: RPAREN
            _: -1
        kinds.append(kind)
        if kind != SKIP:
            prev = kind
        i += 1
    return kinds


def evaluate(codes: List[int]) -> Result[int, str]:
    kinds = tokenize(codes)
    values: List[int] = []
    ops: List[int] = []
    nv = 0
    no = 0
    i = 0
    j = 0
    m = len(kinds)
    # Declared up front (assignments nested in loops below would otherwise
    # read as uses-before-declaration in Rust and infer as Any in V) with
    # no initializer: all three backends leave it unassigned until the first
    # reduce, which dominates every use.
    r: Result[int, str]
    while j < m:
        kind = kinds[j]
        if kind == SKIP:
            i += 1
            j += 1
            continue
        if kind == NUM:
            value = 0
            while j < m:
                if kinds[j] != NUM:
                    break
                value = value * 10 + digit_value(codes[i])
                i += 1
                j += 1
            if nv < len(values):
                values[nv] = value
            else:
                values.append(value)
            nv += 1
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
                r = apply_op(ops[no - 1], values[nv], values[nv + 1])
                if r.is_ok():
                    values[nv] = r.unwrap_or(0)
                    nv += 1
                else:
                    return r
                no -= 1
            no -= 1
        else:
            while no > 0:
                if ops[no - 1] == LPAREN:
                    break
                if precedence(ops[no - 1]) < precedence(kind):
                    break
                nv -= 2
                r = apply_op(ops[no - 1], values[nv], values[nv + 1])
                if r.is_ok():
                    values[nv] = r.unwrap_or(0)
                    nv += 1
                else:
                    return r
                no -= 1
            if no < len(ops):
                ops[no] = kind
            else:
                ops.append(kind)
            no += 1
        i += 1
        j += 1
    while no > 0:
        nv -= 2
        r = apply_op(ops[no - 1], values[nv], values[nv + 1])
        if r.is_ok():
            values[nv] = r.unwrap_or(0)
            nv += 1
        else:
            return r
        no -= 1
    if nv == 0:
        return Error("empty expression")
    return Ok(values[0])


if __name__ == "__main__":
    # "2+3*4"
    print(evaluate([50, 43, 51, 42, 52]).unwrap_or(-999))
    # "(2+3)*4"
    print(evaluate([40, 50, 43, 51, 41, 42, 52]).unwrap_or(-999))
    # "10-8//2"
    print(evaluate([49, 48, 45, 56, 47, 47, 50]).unwrap_or(-999))
    # "7*8+9"
    print(evaluate([55, 42, 56, 43, 57]).unwrap_or(-999))
    # "((2+3)*4)-6"
    print(evaluate([40, 40, 50, 43, 51, 41, 42, 52, 41, 45, 54]).unwrap_or(-999))
    # "10/0" -- division by zero
    print(evaluate([49, 48, 47, 48]).unwrap_or(-999))
