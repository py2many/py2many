set_option linter.unusedVariables false

def main_func : IO Unit := do
  let mut ands : List Bool := []
  let mut ors : List Bool := []
  let mut xors : List Bool := []
  for a in [false, true]do
    for b in [false, true]do
      ands := ands ++ [(a && b)]
      ors := ors ++ [(a || b)]
      xors := xors ++ [(xor a b)]
  assert! ands == [false, false, false, true]
  assert! ors == [false, true, true, true]
  assert! xors == [false, true, true, false]
  IO.println "OK"

def main : IO Unit := do
  main_func
