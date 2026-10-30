from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from typing import List

NUM: int = 0
PLUS: int = 1
MINUS: int = 2
STAR: int = 3
SLASH: int = 4
LPAREN: int = 5
RPAREN: int = 6
SKIP: int = -2


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


def apply_op(op: int, left: int, right: int) -> int:
    match op:
        case 1:
            return left + right
        case 2:
            return left - right
        case 3:
            return left * right
        case 4:
            return left // right
        case _:
            return 0


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


def tokenize(codes: List[int]) -> List[int]:
    kinds: List[int] = []
    i: int = 0
    n = len(codes)
    prev: int = 0
    while i < n:
        code: int = codes[i]
        match code:
            case 48:
                kind = NUM
            case 49:
                kind = NUM
            case 50:
                kind = NUM
            case 51:
                kind = NUM
            case 52:
                kind = NUM
            case 53:
                kind = NUM
            case 54:
                kind = NUM
            case 55:
                kind = NUM
            case 56:
                kind = NUM
            case 57:
                kind = NUM
            case 43:
                kind = PLUS
            case 45:
                kind = MINUS
            case 42:
                kind = STAR
            case 47:
                match prev:
                    case 4:
                        kind = SKIP
                    case _:
                        kind = SLASH
            case 40:
                kind = LPAREN
            case 41:
                kind = RPAREN
            case _:
                kind = -1
        kinds.append(kind)
        if kind != SKIP:
            prev = kind
        i += 1
    return kinds


def evaluate(codes: List[int]) -> int:
    kinds: List[int] = tokenize(codes)
    values: List[int] = []
    ops: List[int] = []
    nv: int = 0
    no: int = 0
    i: int = 0
    j: int = 0
    m = len(kinds)
    while j < m:
        kind: int = kinds[j]
        if kind == SKIP:
            i += 1
            j += 1
            continue
        if kind == NUM:
            value: int = 0
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
        i += 1
        j += 1
    while no > 0:
        nv -= 2
        values[nv] = apply_op(ops[no - 1], values[nv], values[nv + 1])
        nv += 1
        no -= 1
    return values[0]


if __name__ == "__main__":
    print(evaluate([50, 43, 51, 42, 52]))
    print(evaluate([40, 50, 43, 51, 41, 42, 52]))
    print(evaluate([49, 48, 45, 56, 47, 47, 50]))
    print(evaluate([55, 42, 56, 43, 57]))
    print(evaluate([40, 40, 50, 43, 51, 41, 42, 52, 41, 45, 54]))
