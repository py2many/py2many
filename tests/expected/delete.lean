import Std

set_option linter.unusedVariables false

def show_ : IO Unit := do
  let mut my_list := [1, 2, 3, 4, 5]
  my_list := my_list.eraseIdx 2
  IO.println (toString (my_list).length)
  let mut my_dict : Std.HashMap _ _ := (((({ } : Std.HashMap _ _).insert "a" 1).insert "b" 2).insert "c" 3)
  my_dict := my_dict.erase "b"
  IO.println (toString (my_dict).size)

def main : IO Unit := do
  show_
