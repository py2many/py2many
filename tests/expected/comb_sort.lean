set_option linter.unusedVariables false

def comb_sort (seq : List Nat) : List Nat :=
  Id.run
    (do
      let mut seq := seq
      let mut gap := (seq).length
      let mut swap := true
      while gap > 1 || swap do
        gap := (max 1 (Float.toUInt64 (Float.floor ((Float.ofNat gap) / 1.25))).toNat)
        swap := false
        for i in (List.range ((seq).length - gap)) do
          if seq[i]! > seq[(i + gap)]! then
            let (__tmp1, __tmp2) := (seq[(i + gap)]!, seq[i]!)
            seq := seq.set i __tmp1
            seq := seq.set (i + gap) __tmp2
            swap := true
      return seq)

def main : IO Unit := do
  let mut unsorted := [14, 11, 19, 5, 16, 10, 19, 12, 5, 12]
  let expected := [5, 5, 10, 11, 12, 12, 14, 16, 19, 19]
  assert! (comb_sort unsorted) == expected
  IO.println "OK"
