set_option linter.unusedVariables false

def main_func : IO Unit := do
  (IO.print "foobar\n")

def main : IO Unit := do
  main_func
