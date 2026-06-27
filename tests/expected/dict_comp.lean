import Std

set_option linter.unusedVariables false

def show_ : IO Unit := do
  let squares : Std.HashMap _ _ := ((List.range 5)).foldl (fun acc x => acc.insert x (x * x)) ({ } : Std.HashMap _ _)
  IO.println (toString (squares).size)
  let evens : Std.HashMap _ _ :=
    (((List.range 10)).filter (fun x => (x % 2) == 0)).foldl (fun acc x => acc.insert x (x * 2)) ({ } : Std.HashMap _ _)
  IO.println (toString (evens).size)

def main : IO Unit := do
  show_
