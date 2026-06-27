import Std

set_option linter.unusedVariables false

def do_unsupported : IO Unit := do
  let a := 1
  let _ :=
    ((({ } : Std.HashMap _ _)).toList).foldl (fun acc (key, value) => acc.insert (key + 1) (value + 1))
      ({ } : Std.HashMap _ _)
  let b := (a != 0)
  IO.println (toString (if b then "True" else "False"))

def main : IO Unit := do
  do_unsupported
