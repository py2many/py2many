set_option linter.unusedVariables false

partial def fib (i : Nat) : Nat :=
  Id.run
    (do
      if h1 : (i == 0 || i == 1) then
        return 1
      return ((fib (i - 1)) + (fib (i - 2))))

def main : IO Unit := do
  IO.println (toString (fib 5))
