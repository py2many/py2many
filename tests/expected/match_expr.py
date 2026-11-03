from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from typing import Dict, List, Tuple
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


def digit_value(code: int) -> int:
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
            return -1


def apply_float(
    op: Token, l: Result[float, str], r: Result[float, str]
) -> Result[float, str]:
    if l.is_ok():
        if r.is_ok():
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
                    return (
                        Ok(left / right) if right != 0.0 else Error("Division by zero")
                    )
                case _:
                    return Ok(0.0)
        return r
    return l


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
    vals: List[float] = []
    i: int = 0
    n = len(codes)
    while i < n:
        code: int = codes[i]
        digit: int = digit_value(code)
        if digit >= 0:
            value: float = 0.0
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
    toks: List[Token] = []
    i: int = 0
    n = len(codes)
    prev_slash: bool = False
    while i < n:
        code: int = codes[i]
        if code == ord("/") and prev_slash:
            i += 1
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
        i += 1
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
        case _:
            return Error("unknown expression")


def parse(toks: List[Token], tvals: List[float]) -> List[Expr]:
    nodes: List[Expr] = []
    ops: List[Token] = []
    nv: int = 0
    no: int = 0
    k: int = 0
    j: int = 0
    m = len(toks)
    op: Token
    node: Expr
    while j < m:
        if toks[j].is_skip():
            j += 1
            continue
        if toks[j].is_num():
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
                ops[no] = Token.LPAREN("(")
            else:
                ops.append(Token.LPAREN("("))
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
    toks: List[Token] = tokenize(codes)
    tvals: List[float] = number_values(codes)
    nodes: List[Expr] = parse(toks, tvals)
    if len(nodes) == 0:
        return Error("empty expression")
    return eval_expr(nodes[0], env)


if __name__ == "__main__":
    env: Dict[str, float] = {"x": 5.0}
    print(int(evaluate([50, 43, 51, 42, 52], env).unwrap_or(-999.0)))
    print(int(evaluate([40, 50, 43, 51, 41, 42, 52], env).unwrap_or(-999.0)))
    print(int(evaluate([49, 48, 45, 56, 47, 47, 50], env).unwrap_or(-999.0)))
    print(int(evaluate([55, 42, 56, 43, 57], env).unwrap_or(-999.0)))
    print(
        int(
            evaluate([40, 40, 50, 43, 51, 41, 42, 52, 41, 45, 54], env).unwrap_or(
                -999.0
            )
        )
    )
    print(int(evaluate([49, 48, 47, 48], env).unwrap_or(-999.0)))
    print(
        int(
            eval_expr(Expr.ADD(Expr.VARIABLE("x"), Expr.NUMBER(1.0)), env).unwrap_or(
                -999.0
            )
        )
    )
