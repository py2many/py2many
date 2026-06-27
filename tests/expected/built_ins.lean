set_option linter.unusedVariables false

def default_builtins : IO Unit := do
  let a := ""
  let b := false
  let c := 0
  let d : Float := 0.0
  assert! a == ""
  assert! b == false
  assert! c == 0
  assert! d == 0.0

def main : IO Unit := do
  let a := (max 1 2)
  IO.println (toString a)
  let b := (min 1 2)
  IO.println (toString b)
  let c := ((min 1.0 2.0)).toUInt64.toNat
  IO.println (toString c)
