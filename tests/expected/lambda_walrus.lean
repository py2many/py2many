set_option linter.unusedVariables false

def show_ : IO Unit := do
  let f := (fun x => (x + 1))
  IO.println (toString (f 5))
  let nums := [1, 2, 3]
  let result := ((nums).map (fun x => (x * 2)))
  IO.println (toString (result).length)

def main : IO Unit := do
  show_
