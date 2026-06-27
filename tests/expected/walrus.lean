set_option linter.unusedVariables false

def show_ : IO Unit := do
  let n := ([1, 2, 3]).length
  if n > 2 then
    IO.println (toString n)
  let mut i := 0
  while true do
    let x := (i * 2)
    if !(x < 10) then
      break
    IO.println (toString x)
    i := i + 1

def main : IO Unit := do
  show_
