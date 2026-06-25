set_option linter.unusedVariables false

def global_var :=
  10

def test_global : IO Unit := do
  let global_var := 20
  IO.println (toString global_var)

def show_ : IO Unit := do
  test_global

def main : IO Unit := do
  show_
