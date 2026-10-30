from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from typing import Tuple
from functools import reduce
from itertools import groupby
from typing import Dict, List, Optional
from adt import adt as sealed
from py2many.result import Error, Ok, Result


@sealed
class Token:
    NUM: int
    PLUS: int
    MINUS: int
    STAR: int
    SLASH: int
    LPAREN: int
    RPAREN: int
    SKIP: int


@sealed
class Expr:
    NUMBER: float
    VARIABLE: str
    ADD: Tuple["Expr", "Expr"]
    SUBTRACT: Tuple["Expr", "Expr"]
    MULTIPLY: Tuple["Expr", "Expr"]
    DIVIDE: Tuple["Expr", "Expr"]


def digit_value(code: int) -> Optional[int]:
    match code:
        case 48:
            return 0
        case 49:
            return 1
        case 50:
            return 2
        case 51:
            return 3
        case 52:
            return 4
        case 53:
            return 5
        case 54:
            return 6
        case 55:
            return 7
        case 56:
            return 8
        case 57:
            return 9
        case _:
            return None


def apply_float(
    op: Token, l: Result[float, str], r: Result[float, str]
) -> Result[float, str]:
    if not l.is_ok():
        return l
    if not r.is_ok():
        return r
    left = l.unwrap_or(0.0)
    right = r.unwrap_or(0.0)
    match op:
        case _ if op.is_plus():
            return Ok(left + right)
        case _ if op.is_minus():
            return Ok(left - right)
        case _ if op.is_star():
            return Ok(left * right)
        case _ if op.is_slash():
            return Ok(left / right) if right != 0.0 else Error("Division by zero")
        case _:
            return Ok(0.0)


def precedence(op: Token) -> int:
    match op:
        case _ if op.is_star():
            return 2
        case _ if op.is_slash():
            return 2
        case _ if op.is_plus():
            return 1
        case _ if op.is_minus():
            return 1
        case _:
            return 0


def number_values(codes: List[int]) -> List[float]:
    digit_runs = [
        list(g)
        for is_digit, g in groupby(codes, lambda c: digit_value(c) is not None)
        if is_digit
    ]
    return [
        reduce(lambda acc, c: acc * 10.0 + float(digit_value(c)), run, 0.0)
        for run in digit_runs
    ]


def tokenize(codes: List[int]) -> List[Token]:
    toks: List[Token] = []
    prev_slash: bool = False
    for code in codes:
        if code == ord("/") and prev_slash:
            continue
        match code:
            case 48:
                tok = Token.NUM("0")
            case 49:
                tok = Token.NUM("0")
            case 50:
                tok = Token.NUM("0")
            case 51:
                tok = Token.NUM("0")
            case 52:
                tok = Token.NUM("0")
            case 53:
                tok = Token.NUM("0")
            case 54:
                tok = Token.NUM("0")
            case 55:
                tok = Token.NUM("0")
            case 56:
                tok = Token.NUM("0")
            case 57:
                tok = Token.NUM("0")
            case 43:
                tok = Token.PLUS("+")
            case 45:
                tok = Token.MINUS("-")
            case 42:
                tok = Token.STAR("*")
            case 47:
                tok = Token.SLASH("/")
            case 40:
                tok = Token.LPAREN("(")
            case 41:
                tok = Token.RPAREN(")")
            case _:
                tok = Token.SKIP(0)
        prev_slash = tok.is_slash() if not tok.is_skip() else prev_slash
        toks.append(tok)
    return toks


def lookup(env: Dict[str, float], name: str) -> Result[float, str]:
    if name in env:
        return Ok(env[name])
    return Error("undefined variable")


def make_node(op: Token, left: Expr, right: Expr) -> Expr:
    match op:
        case _ if op.is_plus():
            return Expr.ADD(left, right)
        case _ if op.is_minus():
            return Expr.SUBTRACT(left, right)
        case _ if op.is_star():
            return Expr.MULTIPLY(left, right)
        case _ if op.is_slash():
            return Expr.DIVIDE(left, right)
        case _:
            return Expr.NUMBER(0.0)


def reduce_top(ops: List[Token], nodes: List[Expr]) -> bool:
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
    match e:
        case _ if e.is_number():
            n = e.number()
            return Ok(n)
        case _ if e.is_variable():
            name = e.variable()
            return lookup(env, name)
        case _ if e.is_add():
            l, r = e.add()
            return apply_float(Token.PLUS("+"), eval_expr(l, env), eval_expr(r, env))
        case _ if e.is_subtract():
            l, r = e.subtract()
            return apply_float(Token.MINUS("-"), eval_expr(l, env), eval_expr(r, env))
        case _ if e.is_multiply():
            l, r = e.multiply()
            return apply_float(Token.STAR("*"), eval_expr(l, env), eval_expr(r, env))
        case _ if e.is_divide():
            l, r = e.divide()
            return apply_float(Token.SLASH("/"), eval_expr(l, env), eval_expr(r, env))


def parse(toks: List[Token], tvals: List[float]) -> List[Expr]:
    nodes: List[Expr] = []
    ops: List[Token] = []
    values = iter(tvals)
    in_number_run: bool = False
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
            ops.append(Token.LPAREN("("))
        elif tok.is_rparen():
            while len(ops) > 0 and (not ops[-1].is_lparen()):
                if not reduce_top(ops, nodes):
                    break
            if len(ops) > 0 and ops[-1].is_lparen():
                ops.pop()
        else:
            op: Token = tok
            while (
                len(ops) > 0
                and (not ops[-1].is_lparen())
                and (precedence(ops[-1]) >= precedence(op))
            ):
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
    toks: List[Token] = tokenize(codes)
    tvals: List[float] = number_values(codes)
    nodes: List[Expr] = parse(toks, tvals)
    if len(nodes) == 0:
        return Error("empty expression")
    return eval_expr(nodes[0], env)


if __name__ == "__main__":
    env: Dict[str, float] = {"x": 5.0}
    for src in ["2+3*4", "(2+3)*4", "10-8//2", "7*8+9", "((2+3)*4)-6", "10/0"]:
        print(int(evaluate(list(map(ord, src)), env).unwrap_or(-999.0)))
    print(
        int(
            eval_expr(Expr.ADD(Expr.VARIABLE("x"), Expr.NUMBER(1.0)), env).unwrap_or(
                -999.0
            )
        )
    )
