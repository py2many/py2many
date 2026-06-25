import Std

def floatToString (f : Float) : String :=
  let s := toString f
  if s.contains (Char.ofNat 46) then
    let trimmed := (s.dropEndWhile (· == Char.ofNat 48)).toString
    if trimmed.endsWith "." then trimmed ++ "0" else trimmed
  else s

set_option linter.unusedVariables false

def inline_pass : IO Unit := do
  pure ()

def inline_ellipsis : IO Unit := do
  pure ()

def indexing : Nat :=
  Id.run
    (do
      let mut sum := 0
      let mut a : List Nat := []
      for i in (List.range 10) do
        a := a ++ [i]
        sum := sum + a[i]!
      return sum)

def infer_bool (code : Nat) : Bool :=
  ([1, 2, 4]).contains code

def show_ : IO Unit := do
  let mut a1 := 10
  let b1 := 15
  let b2 := 15
  assert! b1 == 15
  assert! b2 == 15
  let b9 := 2
  let b10 := 2
  assert! b9 == b10
  let a2 : Float := 2.1
  IO.println (floatToString a2)
  for i in (List.range' 0 (10 - 0)) do
    IO.println (toString i)
  for i in (List.range' 0 ((10 - 0) / 2) 2) do
    IO.println (toString i)
  let a3 := (-(Int.ofNat a1))
  let a4 := (a3 + a1)
  IO.println (toString a4)
  let t1 := (if a1 > 5 then 10 else 5)
  assert! t1 == 10
  let sum1 := indexing
  IO.println (toString sum1)
  let a5 := [1, 2, 3]
  IO.println (toString (a5).length)
  let a9 : List String := ["a", "b", "c", "d"]
  IO.println (toString (a9).length)
  let a7 : Std.HashMap _ _ := ((({ } : Std.HashMap _ _).insert "a" 1).insert "b" 2)
  IO.println (toString (a7).size)
  let a8 := true
  if a8 then
    IO.println "true"
  else
    if a4 > 0 then
      IO.println "never get here"
  if a1 == 11 then
    IO.println "false"
  else
    IO.println "true"
  if true then
    IO.println "World is sane"
  IO.println (toString (if true then "True" else "False"))
  if true then
    a1 := a1 + 1
  assert! a1 == 11
  if true then
    IO.println "true"
  inline_pass
  let s := "1    2"
  IO.println (toString s)
  assert! (infer_bool 1)
  let _escape_quotes := " foo \"bar\" baz "
  assert! ("aaabbccc".contains "bbc")
  assert! (1 != 0)
  let (_c1, _, _c2) := (1, 2, 3)

def main : IO Unit := do
  show_
