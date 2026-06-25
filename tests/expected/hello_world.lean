set_option linter.unusedVariables false

def main : IO Unit := do
  IO.println "Hello world!"
  IO.println (String.intercalate " " ["Hello", "world!"])
