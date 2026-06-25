set_option linter.unusedVariables false

def code_0 :=
  0

def code_1 :=
  1

def l_a :=
  [code_0, code_1]

def code_a :=
  "a"

def code_b :=
  "b"

def l_b :=
  [code_a, code_b]

def main : IO Unit := do
  for i in l_a do
    IO.println (toString i)
  for j in l_b do
    IO.println (toString j)
  if (["a", "b"]).contains "a" then
    IO.println "OK"
