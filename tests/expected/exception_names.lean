set_option linter.unusedVariables false

def show_ : IO Unit := do
  try
    let _ := (3 / 0)
  catch _ =>
    IO.println "ZeroDivisionError"

def main : IO Unit := do
  show_
