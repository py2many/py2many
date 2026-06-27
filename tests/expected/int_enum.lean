import Std

set_option linter.unusedVariables false

inductive Colors where
  | RED
  | GREEN
  | BLUE
  deriving BEq, Repr

def Colors.toNat : Colors → Nat
  | .RED => 1
  | .GREEN => 2
  | .BLUE => 3

instance : Hashable Colors where hash v := hash v.toNat

inductive Permissions where
  | R
  | W
  | X
  deriving BEq, Repr

def Permissions.toNat : Permissions → Nat
  | .R => 1
  | .W => 2
  | .X => 16

instance : Hashable Permissions where hash v := hash v.toNat

def show_ : IO Unit := do
  let color_map : Std.HashMap _ _ :=
    (((({ } : Std.HashMap _ _).insert Colors.RED "red").insert Colors.GREEN "green").insert Colors.BLUE "blue")
  let a := Colors.GREEN
  if a == Colors.GREEN then
    IO.println "green"
  else
    IO.println "Not green"
  let b := Permissions.R
  if b == Permissions.R then
    IO.println "R"
  else
    IO.println "Not R"
  assert! (color_map).size != 0

def main : IO Unit := do
  show_
