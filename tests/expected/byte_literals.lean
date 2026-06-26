set_option linter.unusedVariables false

def main : IO Unit := do
  assert! (⟨#[102, 111, 111]⟩ : ByteArray) != (⟨#[98, 97, 114]⟩ : ByteArray)
  assert! (⟨#[34]⟩ : ByteArray) == (⟨#[34]⟩ : ByteArray)
  assert! (⟨#[39]⟩ : ByteArray) == (⟨#[39]⟩ : ByteArray)
  assert! (⟨#[187, 102, 111, 111]⟩ : ByteArray) == (⟨#[187, 102, 111, 111]⟩ : ByteArray)
  IO.println "OK"
