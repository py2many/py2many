import Std

set_option linter.unusedVariables false

def nested_containers : Bool :=
  Id.run
    (do
      let CODES : Std.HashMap _ _ := (({ } : Std.HashMap _ _).insert "KEY" [1, 3])
      return (CODES["KEY"]!).contains 1)

def main : IO Unit := do
  if nested_containers then
    IO.println "OK"
