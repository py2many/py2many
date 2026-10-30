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

and the parsed program is a recursive expression tree::

    @sealed
    class Expr:
        NUMBER: float
        VARIABLE: str
        ADD: BinOp
        ...

A ``tokenize`` lexer turns character codes into tokens with a large
match that constructs one variant per arm, a ``parse`` shunting-yard
pass builds the tree, and a recursive ``eval_expr`` evaluates it by
dispatching on variant with ``is_*`` checks, e.g.::

    tok = match code:
        43: Token.PLUS()
        47: Token.SLASH()
        _: Token.SKIP()

    j = 0
    while j < m:  # indexed: binding tokens would move them in Rust
        ...

    if e.is_add():
        b_add = e.add()
        return combine(PLUS, eval_expr(b_add.left, env), eval_expr(b_add.right, env))

A ``/`` following another ``/`` is the second half of ``//``, not
division: it is skipped before the match when the previous token was a
slash. Numbers are lexed by a second pass (``number_values``) into a
parallel list of values.

Per the static-python rules, fallible functions return ``Result[V, E]``
instead of raising: applying ``//`` to zero yields ``Err``, an unknown
variable yields ``Err``, and the caller prints with ``unwrap_or``::

    return match op:
        4: Ok(left / right) if right != 0.0 else Error("Division by zero")
        _: Ok(0.0)

The parser consumes a list of character codes (``[50, 43, 51]`` is
``"2+3"``), so the same source transpiles to Rust, V and CPython (whose
``match`` statement the python backend emits directly).
"""

from dataclasses import dataclass
from typing import Dict, List

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


@dataclass
class BinOp:
    left: "Expr"
    right: "Expr"


@sealed
class Expr:
    NUMBER: float
    VARIABLE: str
    ADD: BinOp
    SUBTRACT: BinOp
    MULTIPLY: BinOp
    DIVIDE: BinOp


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


def apply_float(op: int, left: float, right: float) -> Result[float, str]:
    return match op:
        1: Ok(left + right)
        2: Ok(left - right)
        3: Ok(left * right)
        4: Ok(left / right) if right != 0.0 else Error("Division by zero")
        _: Ok(0.0)


def precedence(op: int) -> int:
    return match op:
        3: 2
        4: 2
        1: 1
        2: 1
        _: 0


def number_values(codes: List[int]) -> List[float]:
    # Lex the multi-digit numbers in order; the k-th NUM token takes the
    # k-th value. A separate pass because a match arm is a single
    # expression and cannot run the lexing loop.
    vals: List[float] = []
    i = 0
    n = len(codes)
    while i < n:
        code = codes[i]
        digit = digit_value(code)
        if digit >= 0:
            value = 0.0
            while i < n:
                digit = digit_value(codes[i])
                if digit < 0:
                    break
                value = value * 10.0 + float(digit)
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


def lookup(env: Dict[str, float], name: str) -> Result[float, str]:
    if name in env:
        return Ok(env[name])
    return Error("undefined variable")


def combine(
    op: int, l: Result[float, str], r: Result[float, str]
) -> Result[float, str]:
    if l.is_ok():
        if r.is_ok():
            return apply_float(op, l.unwrap_or(0.0), r.unwrap_or(0.0))
        return r
    return l


def make_node(op: int, left: Expr, right: Expr) -> Expr:
    return match op:
        1: Expr.ADD(BinOp(left, right))
        2: Expr.SUBTRACT(BinOp(left, right))
        3: Expr.MULTIPLY(BinOp(left, right))
        4: Expr.DIVIDE(BinOp(left, right))
        _: Expr.NUMBER(0.0)


def eval_expr(e: Expr, env: Dict[str, float]) -> Result[float, str]:
    if e.is_number():
        return Ok(e.number())
    elif e.is_variable():
        return lookup(env, e.variable())
    elif e.is_add():
        b_add = e.add()
        return combine(
            PLUS, eval_expr(b_add.left, env), eval_expr(b_add.right, env)
        )
    elif e.is_subtract():
        b_subtract = e.subtract()
        return combine(
            MINUS, eval_expr(b_subtract.left, env), eval_expr(b_subtract.right, env)
        )
    elif e.is_multiply():
        b_multiply = e.multiply()
        return combine(
            STAR, eval_expr(b_multiply.left, env), eval_expr(b_multiply.right, env)
        )
    elif e.is_divide():
        b_divide = e.divide()
        return combine(
            SLASH, eval_expr(b_divide.left, env), eval_expr(b_divide.right, env)
        )
    else:
        return Error("unknown expression")


def parse(toks: List[Token], tvals: List[float]) -> List[Expr]:
    # Shunting-yard pass building the expression tree. Nodes pile up in a
    # stack (like values in an evaluator); the single root stays on top.
    nodes: List[Expr] = []
    ops: List[int] = []
    nv = 0
    no = 0
    k = 0
    j = 0
    m = len(toks)
    # Declared up front with no initializer: assignments below are nested
    # in loops/branches, and every use is dominated by an assignment.
    op: int
    node: Expr
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
            if nv < len(nodes):
                nodes[nv] = Expr.NUMBER(tvals[k])
            else:
                nodes.append(Expr.NUMBER(tvals[k]))
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
                node = make_node(ops[no - 1], nodes[nv], nodes[nv + 1])
                if nv < len(nodes):
                    nodes[nv] = node
                else:
                    nodes.append(node)
                nv += 1
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
                node = make_node(ops[no - 1], nodes[nv], nodes[nv + 1])
                if nv < len(nodes):
                    nodes[nv] = node
                else:
                    nodes.append(node)
                nv += 1
                no -= 1
            if no < len(ops):
                ops[no] = op
            else:
                ops.append(op)
            no += 1
        j += 1
    while no > 0:
        nv -= 2
        node = make_node(ops[no - 1], nodes[nv], nodes[nv + 1])
        if nv < len(nodes):
            nodes[nv] = node
        else:
            nodes.append(node)
        nv += 1
        no -= 1
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
    # "2+3*4"
    print(int(evaluate([50, 43, 51, 42, 52], env).unwrap_or(-999.0)))
    # "(2+3)*4"
    print(int(evaluate([40, 50, 43, 51, 41, 42, 52], env).unwrap_or(-999.0)))
    # "10-8//2"
    print(int(evaluate([49, 48, 45, 56, 47, 47, 50], env).unwrap_or(-999.0)))
    # "7*8+9"
    print(int(evaluate([55, 42, 56, 43, 57], env).unwrap_or(-999.0)))
    # "((2+3)*4)-6"
    print(int(evaluate([40, 40, 50, 43, 51, 41, 42, 52, 41, 45, 54], env).unwrap_or(-999.0)))
    # "10/0" -- division by zero
    print(int(evaluate([49, 48, 47, 48], env).unwrap_or(-999.0)))
    # x + 1 -- variable from the environment
    print(int(eval_expr(Expr.ADD(BinOp(Expr.VARIABLE("x"), Expr.NUMBER(1.0))), env).unwrap_or(-999.0)))
