set_option linter.unusedVariables false

def compare_with_integer_variable : IO Unit := do
  let i : Nat := 0
  let mut s : Nat := 1
  if i != 0 then
    s := 2
  else
    s := 3
  assert! s == 3

def use_zero_for_comparison : IO Unit := do
  let i : Nat := 0
  let mut s : Nat := 1
  if 0 != 0 then
    s := 2
  else
    s := 3
  assert! s == 3

def main : IO Unit := do
  compare_with_integer_variable
  use_zero_for_comparison
  IO.println "OK"
