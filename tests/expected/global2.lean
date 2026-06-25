import Std

set_option linter.unusedVariables false

def code_0 :=
  0

def code_1 :=
  1

def code_a :=
  "a"

def code_b :=
  "b"

def l_b :=
  [code_a]

def l_c :=
  (({ } : Std.HashMap _ _).insert code_b code_0)

def main : IO Unit := do
  assert! (l_b).contains "a"
  IO.println "OK"
