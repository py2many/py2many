set_option linter.unusedVariables false

def show_ : IO Unit := do
  let a := 1
  let b := (if ([2, 3]).contains a then 2 else 3)
  IO.println (toString b)

def main : IO Unit := do
  show_
