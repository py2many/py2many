set_option linter.unusedVariables false

def show_ : IO Unit := do
  let f := (fun x => (x + 1))
  IO.println (toString (f 5))

def main : IO Unit := do
  show_
