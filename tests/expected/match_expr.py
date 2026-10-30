from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from typing import List
from adt import adt as sealed
from py2many.result import Error, Ok, Result

PLUS: int = 1
MINUS: int = 2
STAR: int = 3
SLASH: int = 4
LPAREN: int = 5
RPAREN: int = 6


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


def apply_op(op: int, left: int, right: int) -> Result[int, str]:
    match op:
        case 1:
            return Ok(left + right)
        case 2:
            return Ok(left - right)
        case 3:
            return Ok(left * right)
        case 4:
            return Ok(left // right) if right != 0 else Error("Division by zero")
        case _:
            return Ok(0)


def precedence(op: int) -> int:
    match op:
        case 3:
            return 2
        case 4:
            return 2
        case 1:
            return 1
        case 2:
            return 1
        case _:
            return 0


def number_values(codes: List[int]) -> List[int]:
    vals: List[int] = []
    i: int = 0
    n = len(codes)
    while i < n:
        code: int = codes[i]
        digit: int = digit_value(code)
        if digit >= 0:
            value: int = 0
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
    toks: List[Token] = []
    i: int = 0
    n = len(codes)
    prev_slash: bool = False
    while i < n:
        code: int = codes[i]
        if code == 47 and prev_slash:
            i += 1
            continue
        match code:
            case 48:
                tok = Token.NUM()
            case 49:
                tok = Token.NUM()
            case 50:
                tok = Token.NUM()
            case 51:
                tok = Token.NUM()
            case 52:
                tok = Token.NUM()
            case 53:
                tok = Token.NUM()
            case 54:
                tok = Token.NUM()
            case 55:
                tok = Token.NUM()
            case 56:
                tok = Token.NUM()
            case 57:
                tok = Token.NUM()
            case 43:
                tok = Token.PLUS()
            case 45:
                tok = Token.MINUS()
            case 42:
                tok = Token.STAR()
            case 47:
                tok = Token.SLASH()
            case 40:
                tok = Token.LPAREN()
            case 41:
                tok = Token.RPAREN()
            case _:
                tok = Token.SKIP()
        prev_slash = tok.is_slash() if not tok.is_skip() else prev_slash
        toks.append(tok)
        i += 1
    return toks


def evaluate(codes: List[int]) -> Result[int, str]:
    toks: List[Token] = tokenize(codes)
    tvals: List[int] = number_values(codes)
    values: List[int] = []
    ops: List[int] = []
    nv: int = 0
    no: int = 0
    k: int = 0
    op: int
    r: Result[int, str]
    j: int = 0
    m = len(toks)
    while j < m:
        if toks[j].is_skip():
            j += 1
            continue
        if toks[j].is_num():
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
    print(evaluate([50, 43, 51, 42, 52]).unwrap_or(-999))
    print(evaluate([40, 50, 43, 51, 41, 42, 52]).unwrap_or(-999))
    print(evaluate([49, 48, 45, 56, 47, 47, 50]).unwrap_or(-999))
    print(evaluate([55, 42, 56, 43, 57]).unwrap_or(-999))
    print(evaluate([40, 40, 50, 43, 51, 41, 42, 52, 41, 45, 54]).unwrap_or(-999))
    print(evaluate([49, 48, 47, 48]).unwrap_or(-999))
