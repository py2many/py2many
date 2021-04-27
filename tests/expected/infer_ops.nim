
proc foo() =
  let a = 10
  let b = 20
  let c1 = a + b
  let c2 = a - b
  let c3 = a * b
  let c4 = a / b
  let c5 = -(a)
  let d = 2.0
  let e1 = a + d
  let e2 = a - d
  let e3 = a * d
  let e4 = a / d
  let f = -3.0
  let g = -(a)

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

proc fadd1(x: int8, y: float): float =
  return x + y

proc show() =
  let rv = fadd1(6, 6.0)
  assert(rv == 12)
  echo "OK"

proc main() =
  foo()
  show()

main()
