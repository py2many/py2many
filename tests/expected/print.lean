def floatToString (f : Float) : String :=
  let s := toString f
  if s.contains (Char.ofNat 46) then
    let trimmed := (s.dropEndWhile (· == Char.ofNat 48)).toString
    if trimmed.endsWith "." then trimmed ++ "0" else trimmed
  else s

set_option linter.unusedVariables false

def show_ : IO Unit := do
  IO.println "b"
  IO.println (String.intercalate " " [toString 2, "b"])
  let a : Float := 2.1
  IO.println (floatToString a)
  let b := 2.1
  IO.println (floatToString b)
  let c := true
  IO.println (toString (if c then "True" else "False"))

def main : IO Unit := do
  show_
