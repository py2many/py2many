set_option linter.unusedVariables false

def test : Int :=
  Id.run
    (do
      let a : List Int := [1, 2, 3]
      return a[1]!)

def main : IO Unit := do
  let b := test
  assert! b == 2
  IO.println "OK"
