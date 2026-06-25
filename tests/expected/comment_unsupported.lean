set_option linter.unusedVariables false

def do_unsupported : IO Unit := do
  let a :=
    1
      -- dict comprehension ((key + 1), (value + 1)) unimplemented on line 9:4

  let b := (a != 0)
  IO.println (toString (if b then "True" else "False"))

def main : IO Unit := do
  do_unsupported
