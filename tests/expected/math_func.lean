set_option linter.unusedVariables false

def main_func : IO Unit := do
  let a := (2 ^ 4)
  IO.println (toString a)

def main : IO Unit := do
  main_func
