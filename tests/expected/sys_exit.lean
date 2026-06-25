set_option linter.unusedVariables false

def main : IO Unit := do
  IO.println "OK"
  IO.Process.exit 1
