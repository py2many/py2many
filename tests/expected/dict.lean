import Std

set_option linter.unusedVariables false

def implicit_keys : Bool :=
  Id.run
    (do
      let CODES : Std.HashMap _ _ := (({ } : Std.HashMap _ _).insert "KEY" 1)
      return (CODES).contains "KEY")

def explicit_keys : Bool :=
  Id.run
    (do
      let CODES : Std.HashMap _ _ := (({ } : Std.HashMap _ _).insert "KEY" 1)
      return ((CODES).toList.map Prod.fst).contains "KEY")

def dict_values : Bool :=
  Id.run
    (do
      let CODES : Std.HashMap _ _ := (({ } : Std.HashMap _ _).insert "KEY" 1)
      return ((CODES).toList.map Prod.snd).contains 1)

def return_dict_index_str (key : String) : Nat :=
  Id.run
    (do
      let CODES : Std.HashMap _ _ := (({ } : Std.HashMap _ _).insert "KEY" 1)
      return CODES[key]!)

def return_dict_index_int (key : Nat) : String :=
  Id.run
    (do
      let CODES : Std.HashMap _ _ := (({ } : Std.HashMap _ _).insert 1 "one")
      return CODES[key]!)

def main : IO Unit := do
  assert! implicit_keys
  assert! explicit_keys
  assert! dict_values
  assert! (return_dict_index_str "KEY") == 1
  assert! (return_dict_index_int 1) == "one"
  IO.println "OK"
