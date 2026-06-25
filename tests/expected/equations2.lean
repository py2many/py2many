def floatToString (f : Float) : String :=
  let s := toString f
  if s.contains (Char.ofNat 46) then
    let trimmed := (s.dropEndWhile (· == Char.ofNat 48)).toString
    if trimmed.endsWith "." then trimmed ++ "0" else trimmed
  else s

set_option linter.unusedVariables false

def equation (x : Nat) (y : Nat) : Bool :=
  (x > 2 && y < 10 && (x + (2 * y)) == 7)

def fequation (z : Float) : Bool :=
  Id.run
    (do
      let diff := ((7.0 * z) - 1.0)
      return ((-(0.001)) < diff && diff < 0.001))

def main_func : IO Unit := do
  let x := 7
  let y := 0
  let z := 0.142857
  have _ : (equation x y) = true := by native_decide
  have _ : (fequation z) = true := by native_decide
  IO.println (toString x)
  IO.println (toString y)
  IO.println (floatToString z)

def main : IO Unit := do
  main_func
