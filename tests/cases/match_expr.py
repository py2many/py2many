#!/usr/bin/env python3
"""Tiny arithmetic expression parser and evaluator.

Written in the match-as-expression dialect, shaped like a classic
functional-language front end. Tokens are a sealed sum type (see
https://github.com/py2many/adt)::

    @sealed
    class Token:
        NUM: None
        PLUS: None
        ...

A ``tokenize`` lexer turns character codes into tokens with a large
match that constructs one variant per arm, and ``evaluate`` dispatches
on the token stream with ``is_*`` checks, e.g.::

    tok = match code:
        43: Token.PLUS()
        47: Token.SLASH()
        _: Token.SKIP()

    for tok in toks:
        if tok.is_skip():
            continue
        elif tok.is_rparen():
            ...

A ``/`` following another ``/`` is the second half of ``//``, not
division: it is skipped before the match when the previous token was a
slash. Numbers are lexed by a second pass (``number_values``) into a
parallel list of values.

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

from adt import adt as sealed
from py2many.result import Error, Ok, Result

PLUS = 1
MINUS = 2
STAR = 3
SLASH = 4
LPAREN = 5
RPAREN = 6


@sealed
class Token:
    NUM: None
    PLUS: None
    MINUS: None
    STAR: None
    SLASH: None
    LPAREN: None
    RPAREN: None
    SKIP: None


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


def number_values(codes: List[int]) -> List[int]:
    # Lex the multi-digit numbers in order; the k-th NUM token takes the
    # k-th value. A separate pass because a match arm is a single
    # expression and cannot run the lexing loop.
    vals: List[int] = []
    i = 0
    n = len(codes)
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
                i += 1
            vals.append(value)
        else:
            i += 1
    return vals


def tokenize(codes: List[int]) -> List[Token]:
    # Lex character codes into one token per character, as in a classic
    # functional-language lexer. Each match arm constructs a variant.
    # The second `/` of `//` is skipped before the match when the previous
    # token was a slash, so it is never treated as division.
    toks: List[Token] = []
    i = 0
    n = len(codes)
    prev_slash = False
    while i < n:
        code = codes[i]
        if code == 47 and prev_slash:
            i += 1
            continue
        tok = match code:
            48: Token.NUM()
            49: Token.NUM()
            50: Token.NUM()
            51: Token.NUM()
            52: Token.NUM()
            53: Token.NUM()
            54: Token.NUM()
            55: Token.NUM()
            56: Token.NUM()
            57: Token.NUM()
            43: Token.PLUS()
            45: Token.MINUS()
            42: Token.STAR()
            47: Token.SLASH()
            40: Token.LPAREN()
            41: Token.RPAREN()
            _: Token.SKIP()
        # SKIP tokens preserve the previous slash state, so `///` keeps
        # skipping the same way `//` does.
        prev_slash = tok.is_slash() if not tok.is_skip() else prev_slash
        toks.append(tok)
        i += 1
    return toks


def evaluate(codes: List[int]) -> Result[int, str]:
    toks: List[Token] = tokenize(codes)
    tvals: List[int] = number_values(codes)
    values: List[int] = []
    ops: List[int] = []
    nv = 0
    no = 0
    k = 0
    # Declared up front with no initializer: assignments below are nested
    # in loops/branches, and every use is dominated by an assignment.
    op: int
    r: Result[int, str]
    j = 0
    m = len(toks)
    while j < m:
        if toks[j].is_skip():
            j += 1
            continue
        if toks[j].is_num():
            # One tvals entry per digit run; consume the whole run here.
            while j < m:
                if not toks[j].is_num():
                    break
                j += 1
            if nv < len(values):
                values[nv] = tvals[k]
            else:
                values.append(tvals[k])
            k += 1
            nv += 1
            continue
        if toks[j].is_lparen():
            if no < len(ops):
                ops[no] = LPAREN
            else:
                ops.append(LPAREN)
            no += 1
        elif toks[j].is_rparen():
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
            if toks[j].is_plus():
                op = PLUS
            elif toks[j].is_minus():
                op = MINUS
            elif toks[j].is_star():
                op = STAR
            else:
                op = SLASH
            while no > 0:
                if ops[no - 1] == LPAREN:
                    break
                if precedence(ops[no - 1]) < precedence(op):
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
                ops[no] = op
            else:
                ops.append(op)
            no += 1
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
