set_option linter.unusedVariables false

def foo : IO Unit := do
  let a := 10
  let b := 20
  let _c1 := (a + b)
  let _c2 := (a - b)
  let _c3 := (a * b)
  let _c4 := (a / b)
  let _c5 := (-(Int.ofNat a))
  let d := 2.0
  let _e1 := ((Float.ofNat a) + d)
  let _e2 := ((Float.ofNat a) - d)
  let _e3 := ((Float.ofNat a) * d)
  let _e4 := ((Float.ofNat a) / d)
  let _f := (-(3.0))
  let _g := (-(Int.ofNat a))

def add1 (x : Int8) (y : Int8) : Int16 :=
  ((Int16.ofInt x.toInt) + (Int16.ofInt y.toInt))

def add2 (x : Int16) (y : Int16) : Int32 :=
  ((Int32.ofInt x.toInt) + (Int32.ofInt y.toInt))

def add3 (x : Int32) (y : Int32) : Int64 :=
  ((Int64.ofInt x.toInt) + (Int64.ofInt y.toInt))

def add4 (x : Int64) (y : Int64) : Int64 :=
  (x + y)

def add5 (x : UInt8) (y : UInt8) : UInt16 :=
  ((UInt16.ofNat x.toNat) + (UInt16.ofNat y.toNat))

def add6 (x : UInt16) (y : UInt16) : UInt32 :=
  ((UInt32.ofNat x.toNat) + (UInt32.ofNat y.toNat))

def add7 (x : UInt32) (y : UInt32) : UInt64 :=
  ((UInt64.ofNat x.toNat) + (UInt64.ofNat y.toNat))

def add8 (x : UInt64) (y : UInt64) : UInt64 :=
  (x + y)

def add9 (x : Int8) (y : UInt16) : UInt32 :=
  ((UInt32.ofInt x.toInt) + (UInt32.ofNat y.toNat))

def sub (x : Int8) (y : Int8) : Int8 :=
  (x - y)

def mul (x : Int8) (y : Int8) : Int16 :=
  ((Int16.ofInt x.toInt) * (Int16.ofInt y.toInt))

def fadd1 (x : Int8) (y : Float) : Float :=
  ((Float.ofInt x.toInt) + y)

def show_ : IO Unit := do
  assert! ((fadd1 6 6.0) == (Float.ofNat 12))
  IO.println "OK"

def main : IO Unit := do
  foo
  show_
