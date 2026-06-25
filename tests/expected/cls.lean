set_option linter.unusedVariables false

structure Foo where mk ::

def Foo.bar (self : Foo) : String :=
  "a"

def main : IO Unit := do
  let f := Foo.mk
  let b := f.bar
  IO.println (toString b)
