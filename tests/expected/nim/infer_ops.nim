
proc foo() =
  let a = 10
  let b = 20
  let _ = (a + b)
  let _ = (a - b)
  let _ = (a * b)
  let _ = (a / b)
  let _ = -(a)
  let d = 2.0
  let _ = (float64(a) + d)
  let _ = (float64(a) - d)
  let _ = (float64(a) * d)
  let _ = (float64(a) / d)
  let _ = -3.0
  let _ = -(a)

proc add1(x: int8, y: int8): int16 =
  return int16((x + y))

proc add2(x: int16, y: int16): int32 =
  return int32((x + y))

proc add3(x: int32, y: int32): int64 =
  return int64((x + y))

proc add4(x: int64, y: int64): int64 =
  return (x + y)

proc add5(x: uint8, y: uint8): uint16 =
  return uint16((x + y))

proc add6(x: uint16, y: uint16): uint32 =
  return uint32((x + y))

proc add7(x: uint32, y: uint32): uint64 =
  return uint64((x + y))

proc add8(x: uint64, y: uint64): uint64 =
  return (x + y)

proc add9(x: int8, y: uint16): uint32 =
  return uint32((uint16(x) + y))

proc sub(x: int8, y: int8): int8 =
  return (x - y)

proc mul(x: int8, y: int8): int16 =
  return int16((x * y))

proc fadd1(x: int8, y: float64): float64 =
  return (float64(x) + y)

proc show() =
  assert(fadd1(6, 6.0) == 12)
  echo "OK"

proc main() =
  foo()
  show()

main()
