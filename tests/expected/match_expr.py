from typing import Callable, Dict, List, Set, Optional
from ctypes import c_int8 as i8, c_int16 as i16, c_int32 as i32, c_int64 as i64
from ctypes import c_uint8 as u8, c_uint16 as u16, c_uint32 as u32, c_uint64 as u64
import sys
from typing import List

PLUS: int = 1
MINUS: int = 2
STAR: int = 3
SLASH: int = 4
LPAREN: int = 5
RPAREN: int = 6


def digit_value(code: int) -> int:
    return (
        0
        if code == 48
        else (
            1
            if code == 49
            else (
                2
                if code == 50
                else (
                    3
                    if code == 51
                    else (
                        4
                        if code == 52
                        else (
                            5
                            if code == 53
                            else (
                                6
                                if code == 54
                                else (
                                    7
                                    if code == 55
                                    else 8 if code == 56 else 9 if code == 57 else -1
                                )
                            )
                        )
                    )
                )
            )
        )
    )


def op_kind(code: int) -> int:
    return (
        PLUS
        if code == 43
        else (
            MINUS
            if code == 45
            else (
                STAR
                if code == 42
                else (
                    SLASH
                    if code == 47
                    else LPAREN if code == 40 else RPAREN if code == 41 else -1
                )
            )
        )
    )


def apply_op(op: int, left: int, right: int) -> int:
    return (
        left + right
        if op == 1
        else (
            left - right
            if op == 2
            else left * right if op == 3 else left // right if op == 4 else 0
        )
    )


def precedence(op: int) -> int:
    return 2 if op == 3 else 2 if op == 4 else 1 if op == 1 else 1 if op == 2 else 0


def sign_kind(code: int) -> int:
    return (
        10
        if (__match_subj_0 := (1 if code == 43 else 2 if code == 45 else 0)) == 1
        else 20 if __match_subj_0 == 2 else 0
    )


def prec_pair(op1: int, op2: int) -> int:
    return (
        (
            22
            if (__match_subj_1 := precedence(op2)) == 2
            else 21 if __match_subj_1 == 1 else 20
        )
        if (__match_subj_3 := precedence(op1)) == 2
        else (
            (
                12
                if (__match_subj_2 := precedence(op2)) == 2
                else 11 if __match_subj_2 == 1 else 10
            )
            if __match_subj_3 == 1
            else 0
        )
    )


def evaluate(codes: List[int]) -> int:
    values: List[int] = []
    ops: List[int] = []
    nv: int = 0
    no: int = 0
    i: int = 0
    n = len(codes)
    prev: int = 0
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
            if nv < len(values):
                values[nv] = value
            else:
                values.append(value)
            nv += 1
            prev = op_kind(code)
            continue
        kind: int = op_kind(code)
        if kind == SLASH and prev == SLASH:
            i += 1
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
        prev = kind
        i += 1
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
    print(sign_kind(43))
    print(sign_kind(45))
    print(sign_kind(48))
    print(prec_pair(3, 4))
    print(prec_pair(3, 1))
    print(prec_pair(1, 4))
    print(prec_pair(1, 1))
    print(prec_pair(5, 1))
