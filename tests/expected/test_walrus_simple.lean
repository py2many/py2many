set_option linter.unusedVariables false

def show_ : IO Unit := do
  let x := 5
  if x > 3 then
    IO.println (toString x)

def main : IO Unit := do
  show_
