set_option linter.unusedVariables false
  -- This file implements a rectangle class


structure Rectangle where
  height : Nat
  length : Nat
  deriving BEq, Repr

def Rectangle.is_square (self : Rectangle) : Bool :=
  self.height == self.length

def show_ : IO Unit := do
  let mut r := { height := 1, length := 1 : Rectangle }
  assert! r.is_square
  r := { height := 1, length := 2 : Rectangle }
  assert! !(r.is_square)
  IO.println (toString r.height)
  IO.println (toString r.length)

def main : IO Unit := do
  show_
