set_option linter.unusedVariables false

def demorgan (a : Bool) (b : Bool) : Bool :=
  (a && b) == !((!(a) || !(b)))

def main_func : IO Unit := do
  have _ : ∀ (a : Bool) (b : Bool), demorgan a b = true := by decide
  IO.println "proven"

def main : IO Unit := do
  main_func
