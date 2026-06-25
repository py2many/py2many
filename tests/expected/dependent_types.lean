set_option linter.unusedVariables false

def Uid :=
  { uid : Nat // 0 < uid ∧ uid < 1000 }

def Score :=
  { s : Nat // 0 ≤ s ∧ s ≤ 100 }

def main_func : IO Unit := do
  let u : Uid := ⟨42, by omega⟩
  let s : Score := ⟨85, by omega⟩
  IO.println (toString u.val)
  IO.println (toString s.val)

def main : IO Unit := do
  main_func
