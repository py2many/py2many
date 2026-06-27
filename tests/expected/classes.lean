set_option linter.unusedVariables false

structure Foo where mk ::

mutual
  def Foo.bar (self : Foo) : Nat :=
    Id.run
      (do
        return self.baz)
  def Foo.baz (self : Foo) : Nat :=
    Id.run
      (do
        return 10)
end

def main : IO Unit := do
  let f := Foo.mk
  let b := f.bar
  IO.println (toString b)
  assert! b == 10
