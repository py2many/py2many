
proc foo() =
    a = 10
    b = 20
    c1 = a + b
    c2 = a - b
    c3 = a * b
    c4 = a / b
    c5 = -(a)
    d = 2.0
    e1 = a + d
    e2 = a - d
    e3 = a * d
    e4 = a / d
    f = -3.0
    g = -(a)

proc add1(x: int8, y: int8): int16 =
    return x + y

proc add2(x: int16, y: int16): int32 =
    return x + y

proc add3(x: int32, y: int32): int64 =
    return x + y

proc add4(x: int64, y: int64): int64 =
    return x + y

proc add5(x: uint8, y: uint8): uint16 =
    return x + y

proc add6(x: uint16, y: uint16): uint32 =
    return x + y

proc add7(x: uint32, y: uint32): uint64 =
    return x + y

proc add8(x: uint64, y: uint64): uint64 =
    return x + y

proc add9(x: int8, y: uint16): uint32 =
    return x + y

proc sub(x: int8, y: int8): int8 =
    return x - y

proc mul(x: int8, y: int8): int16 =
    return x * y

proc fadd(x: int8, y: float): float =
    return x + y

