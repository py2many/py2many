set_option linter.unusedVariables false

def test_python (iterations : Nat) : IO Unit := do
  let mut iteration := 0
  let mut total : Float := 0.0
  let array_length := 1000
  let array : List Nat := (List.range array_length)
  IO.println (String.intercalate " " ["iterations", toString iterations])
  while iteration < iterations do
    let mut innerloop := 0
    while innerloop < 100 do
      total := total + (Float.ofNat array[((iteration + innerloop) % array_length)]!)
      innerloop := innerloop + 1
    iteration := iteration + 1
  if (total == (Float.ofNat 15150)) then
    IO.println
        "OK"
          -- del unimplemented for Name(id='array', ctx=Del())


def main : IO Unit := do
  (test_python 3)
