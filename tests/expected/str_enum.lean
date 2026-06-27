import Std

set_option linter.unusedVariables false

inductive Colors where
  | RED
  | GREEN
  | BLUE
  deriving BEq, Repr

def Colors.toString : Colors → String
  | .RED => "red"
  | .GREEN => "green"
  | .BLUE => "blue"

instance : ToString Colors where toString := Colors.toString

instance : Hashable Colors where hash v := hash v.toString

def show_ : IO Unit := do
  let color_map : Std.HashMap _ _ :=
    (((({ } : Std.HashMap _ _).insert Colors.RED "1").insert Colors.GREEN "2").insert Colors.BLUE "3")
  let a := Colors.GREEN
  if a == Colors.GREEN then
    IO.println "green"
  else
    IO.println "Not green"
  IO.println (toString (color_map).size)

def main : IO Unit := do
  show_
