set_option linter.unusedVariables false

def foo : IO Unit := do
  let a := 10
  let b := a
  assert! b == 10
  IO.println (toString b)

def main : IO Unit := do
  foo
