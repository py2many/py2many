set_option linter.unusedVariables false

def main : IO Unit := do
  let a := 10
  IO.println (toString (String.join ["hello ", (toString (a + 1)), " world"]))
