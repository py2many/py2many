set_option linter.unusedVariables false

def show_ : IO Unit := do
  let myfunc := (fun x y => (x + y))
  IO.println (toString (myfunc 1 2))

def main : IO Unit := do
  show_
