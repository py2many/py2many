set_option linter.unusedVariables false

def for_with_break : IO Unit := do
  for i in (List.range 4) do
    if i == 2 then
      break
    IO.println (toString i)

def for_with_continue : IO Unit := do
  for i in (List.range 4) do
    if i == 2 then
      continue
    IO.println (toString i)

def for_with_else : IO Unit := do
  let has_break := false
  for i in (List.range 4) do
    IO.println (toString i)
  if has_break != true then
    IO.println "OK"

def while_with_break : IO Unit := do
  let mut i := 0
  while true do
    if i == 2 then
      break
    IO.println (toString i)
    i := i + 1

def while_with_continue : IO Unit := do
  let mut i := 0
  while i < 5 do
    i := i + 1
    if i == 2 then
      continue
    IO.println (toString i)

def main : IO Unit := do
  for_with_break
  for_with_continue
  for_with_else
  while_with_break
  while_with_continue
