#!/usr/bin/env python3
"""Tiny arithmetic expression parser and evaluator.

Written in the match-as-expression dialect, shaped like a classic
functional-language front end. Tokens are a sealed sum type (see
https://github.com/py2many/adt)::

    @sealed
    class Token:
        NUM: int = '0'
        PLUS: int = '+'
        ...

and the parsed program is a recursive expression tree::

    @sealed
    class Expr:
        NUMBER: float
        VARIABLE: str
        ADD(Expr, Expr)
        ...

A ``tokenize`` lexer turns character codes into tokens with a large
match that constructs one variant per arm, a ``parse`` shunting-yard
pass builds the tree, and a recursive ``eval_expr`` evaluates it by
matching on variant with bindings, e.g.::

    return match e:
        Expr.NUMBER(n): Ok(n)
        Expr.ADD(l, r): apply_float(Token.PLUS(), eval_expr(l, env), eval_expr(r, env))

``ops`` are ``Token``s themselves, not integer codes: there are no
``PLUS = 1`` style constants. ``precedence``, ``apply_float`` and
``make_node`` all take a ``Token`` and match on its variant::

    return match op:
        Token.PLUS(): Expr.ADD(left, right)
        _: Expr.NUMBER(0.0)

Character literals (``'+'``, ``')'``, ``'0'``) stand for their codes:
no magic numbers appear. Token payloads default to their
representative character, so constructions stay nullary
(``Token.PLUS()`` means ``Token.PLUS('+')``).

A ``/`` following another ``/`` is the second half of ``//``, not
division: it is skipped before the match when the previous token was a
slash. Numbers are lexed by a second pass (``number_values``) into a
parallel list of values.

Per the static-python rules, fallible functions return ``Result[V, E]``
instead of raising: applying ``//`` to zero yields ``Err``, an unknown
variable yields ``Err``, and the caller prints with ``unwrap_or``::

    return match op:
        Token.SLASH(): Ok(left / right) if right != 0.0 else Error("Division by zero")
        _: Ok(0.0)

The parser consumes a list of character codes (``[50, 43, 51]`` is
``"2+3"``), so the same source transpiles to Rust, V and CPython (whose
``match`` statement the python backend emits directly).
"""

from typing import Dict, List, Tuple

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


def digit_value(code: int) -> int:
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
        _: -1


def apply_float(op: Token, l: Result[float, str], r: Result[float, str]) -> Result[float, str]:
    if l.is_ok():
        if r.is_ok():
            left = l.unwrap_or(0.0)
            right = r.unwrap_or(0.0)
            return match op:
                Token.PLUS(): Ok(left + right)
                Token.MINUS(): Ok(left - right)
                Token.STAR(): Ok(left * right)
                Token.SLASH(): Ok(left / right) if right != 0.0 else Error("Division by zero")
                _: Ok(0.0)
        return r
    return l


def precedence(op: Token) -> int:
    return match op:
        Token.STAR(): 2
        Token.SLASH(): 2
        Token.PLUS(): 1
        Token.MINUS(): 1
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
        if code == ord('/') and prev_slash:
            i += 1
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


def make_node(op: Token, left: Expr, right: Expr) -> Expr:
    return match op:
        Token.PLUS(): Expr.ADD(left, right)
        Token.MINUS(): Expr.SUBTRACT(left, right)
        Token.STAR(): Expr.MULTIPLY(left, right)
        Token.SLASH(): Expr.DIVIDE(left, right)
        _: Expr.NUMBER(0.0)


def eval_expr(e: Expr, env: Dict[str, float]) -> Result[float, str]:
    return match e:
        Expr.NUMBER(n): Ok(n)
        Expr.VARIABLE(name): lookup(env, name)
        Expr.ADD(l, r): apply_float(Token.PLUS(), eval_expr(l, env), eval_expr(r, env))
        Expr.SUBTRACT(l, r): apply_float(Token.MINUS(), eval_expr(l, env), eval_expr(r, env))
        Expr.MULTIPLY(l, r): apply_float(Token.STAR(), eval_expr(l, env), eval_expr(r, env))
        Expr.DIVIDE(l, r): apply_float(Token.SLASH(), eval_expr(l, env), eval_expr(r, env))
        _: Error("unknown expression")


def parse(toks: List[Token], tvals: List[float]) -> List[Expr]:
    # Shunting-yard pass building the expression tree. Nodes pile up in a
    # stack (like values in an evaluator); the single root stays on top.
    # Operators are Tokens themselves; LPAREN sentinels are tested with
    # is_lparen, so no integer op codes exist.
    nodes: List[Expr] = []
    ops: List[Token] = []
    nv = 0
    no = 0
    k = 0
    j = 0
    m = len(toks)
    # Declared up front with no initializer: assignments below are nested
    # in loops/branches, and every use is dominated by an assignment.
    op: Token
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
                ops[no] = Token.LPAREN()
            else:
                ops.append(Token.LPAREN())
            no += 1
        elif toks[j].is_rparen():
            while no > 0:
                if ops[no - 1].is_lparen():
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
            op = toks[j]
            while no > 0:
                if ops[no - 1].is_lparen():
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
    print(int(eval_expr(Expr.ADD(Expr.VARIABLE("x"), Expr.NUMBER(1.0)), env).unwrap_or(-999.0)))
