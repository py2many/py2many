#!/usr/bin/env python3
"""Tiny arithmetic expression parser and evaluator.

Port of ``match_expr.rs`` back into the match-as-expression hybrid
dialect (cf. ``match_expr.py``). Same sealed sums, same ``match``
expression syntax, but mirroring the idiomatic-Rust structure:

* ``digit_value`` returns ``Optional[int]`` (Rust ``Option<u32>``):
  a digit maps to itself, anything else to ``None``.
* ``number_values`` mirrors Rust
  ``split(filter).map(fold).collect()`` via ``groupby`` + ``reduce``.
* ``tokenize`` mirrors Rust ``iter().scan().flatten().collect()``:
  a stateful scan carrying ``prev_slash``; the second ``/`` of ``//``
  yields nothing, ``SKIP`` preserves the scan state.
* ``parse`` mirrors the Rust ``for &tok in tokens`` loop with an
  ``in_number_run`` flag and a ``values`` iterator -- no ``k``/``j``
  indices.
* ``apply_float`` mirrors Rust ``?`` with early returns, then a single
  ``return match op:`` (guard arm for division by zero).
* ``evaluate`` / ``eval_expr`` mirror Rust exhaustiveness and
  ``let-else`` empty-check.

Character literals (``'+'``, ``')'``, ``'0'``) stand for their codes,
as in ``match_expr.py``. Token payloads default to their representative
character, so constructions stay nullary (``Token.PLUS()``).
"""

from functools import reduce
from itertools import groupby
from typing import Dict, List, Optional

from adt import adt as sealed

from py2many.result import Error, Ok, Result


@sealed
class Token:
    NUM: int = '0'
    PLUS: int = '+'
    MINUS: int = '-'
    STAR: int = '*'
    SLASH: int = '/'
    LPAREN: int = '('
    RPAREN: int = ')'
    SKIP: int = 0


@sealed
class Expr:
    NUMBER: float
    VARIABLE: str
    ADD(Expr, Expr)
    SUBTRACT(Expr, Expr)
    MULTIPLY(Expr, Expr)
    DIVIDE(Expr, Expr)


def digit_value(code: int) -> Optional[int]:
    # Rust: Option<u32> via is_ascii_digit().then(...).
    # Here Some(d) is just d; Rust None is Python None.
    return match code:
        '0': 0
        '1': 1
        '2': 2
        '3': 3
        '4': 4
        '5': 5
        '6': 6
        '7': 7
        '8': 8
        '9': 9
        _: None


def apply_float(op: Token, l: Result[float, str], r: Result[float, str]) -> Result[float, str]:
    # Mirrors Rust `let left = l?; let right = r?; match op { ... }`.
    if not l.is_ok():
        return l
    if not r.is_ok():
        return r
    left = l.unwrap_or(0.0)
    right = r.unwrap_or(0.0)
    return match op:
        Token.PLUS(): Ok(left + right)
        Token.MINUS(): Ok(left - right)
        Token.STAR(): Ok(left * right)
        Token.SLASH(): Ok(left / right) if right != 0.0 else Error("Division by zero")
        _: Ok(0.0)


def precedence(op: Token) -> int:
    # Rust combines the first two / last two arms with `|`; spelled out
    # here in the original dialect's one-variant-per-arm style.
    return match op:
        Token.STAR(): 2
        Token.SLASH(): 2
        Token.PLUS(): 1
        Token.MINUS(): 1
        _: 0


def number_values(codes: List[int]) -> List[float]:
    # Mirrors Rust:
    #   codes.split(is_none).filter(!empty).map(fold).collect()
    # via groupby (split on non-digits) + reduce (fold).
    digit_runs = [list(g) for is_digit, g in groupby(codes, lambda c: digit_value(c) is not None) if is_digit]
    return [reduce(lambda acc, c: acc * 10.0 + float(digit_value(c)), run, 0.0) for run in digit_runs]


def tokenize(codes: List[int]) -> List[Token]:
    # Mirrors Rust `.scan(false, ...).flatten().collect()`: a stateful
    # scan carrying prev_slash. The second `/` of `//` yields nothing
    # (skipped before the match); SKIP preserves the scan state.
    toks: List[Token] = []
    prev_slash = False
    for code in codes:
        if code == ord('/') and prev_slash:
            continue
        tok = match code:
            '0': Token.NUM()
            '1': Token.NUM()
            '2': Token.NUM()
            '3': Token.NUM()
            '4': Token.NUM()
            '5': Token.NUM()
            '6': Token.NUM()
            '7': Token.NUM()
            '8': Token.NUM()
            '9': Token.NUM()
            '+': Token.PLUS()
            '-': Token.MINUS()
            '*': Token.STAR()
            '/': Token.SLASH()
            '(': Token.LPAREN()
            ')': Token.RPAREN()
            _: Token.SKIP()
        # Rust: `if tok != Skip { *prev_slash = tok == Slash }`.
        prev_slash = tok.is_slash() if not tok.is_skip() else prev_slash
        toks.append(tok)
    return toks


def lookup(env: Dict[str, float], name: str) -> Result[float, str]:
    if name in env:
        return Ok(env[name])
    return Error("undefined variable")


def make_node(op: Token, left: Expr, right: Expr) -> Expr:
    return match op:
        Token.PLUS(): Expr.ADD(left, right)
        Token.MINUS(): Expr.SUBTRACT(left, right)
        Token.STAR(): Expr.MULTIPLY(left, right)
        Token.SLASH(): Expr.DIVIDE(left, right)
        _: Expr.NUMBER(0.0)


def reduce_top(ops: List[Token], nodes: List[Expr]) -> bool:
    # Mirrors the Rust helper: pop one operator and two operands,
    # push the combined node; False on underflow (malformed input).
    if len(nodes) < 2:
        return False
    if len(ops) == 0:
        return False
    op = ops.pop()
    right = nodes.pop()
    left = nodes.pop()
    nodes.append(make_node(op, left, right))
    return True


def eval_expr(e: Expr, env: Dict[str, float]) -> Result[float, str]:
    # Exhaustive like the Rust `match`, so no `_` fallback arm.
    return match e:
        Expr.NUMBER(n): Ok(n)
        Expr.VARIABLE(name): lookup(env, name)
        Expr.ADD(l, r): apply_float(Token.PLUS(), eval_expr(l, env), eval_expr(r, env))
        Expr.SUBTRACT(l, r): apply_float(Token.MINUS(), eval_expr(l, env), eval_expr(r, env))
        Expr.MULTIPLY(l, r): apply_float(Token.STAR(), eval_expr(l, env), eval_expr(r, env))
        Expr.DIVIDE(l, r): apply_float(Token.SLASH(), eval_expr(l, env), eval_expr(r, env))


def parse(toks: List[Token], tvals: List[float]) -> List[Expr]:
    # Mirrors the Rust shunting-yard `for &tok in tokens` loop: each
    # maximal Num run forms one node from a single `values` entry;
    # `in_number_run` marks run leaders, `values` is a consumed iterator.
    nodes: List[Expr] = []
    ops: List[Token] = []
    values = iter(tvals)
    in_number_run = False
    for tok in toks:
        if tok.is_num():
            if not in_number_run:
                v = next(values, None)
                if v is not None:
                    nodes.append(Expr.NUMBER(v))
            in_number_run = True
            continue
        in_number_run = False
        if tok.is_skip():
            continue
        if tok.is_lparen():
            ops.append(Token.LPAREN())
        elif tok.is_rparen():
            while len(ops) > 0 and not ops[-1].is_lparen():
                if not reduce_top(ops, nodes):
                    break
            if len(ops) > 0 and ops[-1].is_lparen():
                ops.pop()
        else:
            op = tok
            while len(ops) > 0 and not ops[-1].is_lparen() and precedence(ops[-1]) >= precedence(op):
                if not reduce_top(ops, nodes):
                    break
            ops.append(op)
    while len(ops) > 0:
        if ops[-1].is_lparen():
            ops.pop()
            continue
        if not reduce_top(ops, nodes):
            break
    return nodes


def evaluate(codes: List[int], env: Dict[str, float]) -> Result[float, str]:
    toks = tokenize(codes)
    tvals = number_values(codes)
    nodes = parse(toks, tvals)
    if len(nodes) == 0:
        return Error("empty expression")
    return eval_expr(nodes[0], env)


if __name__ == "__main__":
    env: Dict[str, float] = {"x": 5.0}
    # Mirrors Rust `for src in [...] { evaluate(src.as_bytes()) }`;
    # list(map(ord, src)) is the hybrid's `as_bytes()`.
    for src in ["2+3*4", "(2+3)*4", "10-8//2", "7*8+9", "((2+3)*4)-6", "10/0"]:
        print(int(evaluate(list(map(ord, src)), env).unwrap_or(-999.0)))
    # x + 1 -- variable from the environment
    print(int(eval_expr(Expr.ADD(Expr.VARIABLE("x"), Expr.NUMBER(1.0)), env).unwrap_or(-999.0)))
