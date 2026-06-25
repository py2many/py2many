set_option linter.unusedVariables false

def bubble_sort (seq : List Int) : List Int :=
  Id.run
    (do
      let mut seq := seq
      let L := (seq).length
      for _ in (List.range L) do
        for n in (List.range' 1 (L - 1)) do
          if seq[n]! < seq[(n - 1)]! then
            let (__tmp1, __tmp2) := (seq[n]!, seq[(n - 1)]!)
            seq := seq.set (n - 1) __tmp1
            seq := seq.set n __tmp2
      return seq)

def main : IO Unit := do
  let mut unsorted := [14, 11, 19, 5, 16, 10, 19, 12, 5, 12]
  let expected := [5, 5, 10, 11, 12, 12, 14, 16, 19, 19]
  assert! (bubble_sort unsorted) == expected
  IO.println "OK"
