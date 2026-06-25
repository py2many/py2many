set_option linter.unusedVariables false

def compare_assert (a : Int) (b : Int) : IO Unit := do
  assert! a == b
  assert! !(0 == 1)

def main : IO Unit := do
  assert! true
  assert! !(false)
  (compare_assert 1 1)
  assert! true
  assert! true
  IO.println "OK"
