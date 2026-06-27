set_option linter.unusedVariables false

def bisect_right (data : List Nat) (item : Nat) : Nat :=
  Id.run
    (do
      let mut low := 0
      let mut high : Nat := ((data).length : Nat)
      while low < high do
        let middle := (((low + high) / 2)).toUInt64.toNat
        if item < data[middle]! then
          high := middle
        else
          low := (middle + 1)
      return low)

def bin_it (limits : List Nat) (data : List Nat) : List Nat :=
  Id.run
    (do
      let mut bins := [0]
      for _x in limits do
        bins := bins ++ [0]
      for d in data do
        bins := bins.set (bisect_right limits d) (bins[(bisect_right limits d)]! + 1)
      return bins)

def main : IO Unit := do
  let limits := [23, 37, 43, 53, 67, 83]
  let data :=
    [95, 21, 94, 12, 99, 4, 70, 75, 83, 93, 52, 80, 57, 5, 53, 86, 65, 17, 92, 83, 71, 61, 54, 58, 47, 16, 8, 9, 32, 84,
      7, 87, 46, 19, 30, 37, 96, 6, 98, 40, 79, 97, 45, 64, 60, 29, 49, 36, 43, 55]
  assert! (bin_it limits data) == [11, 4, 2, 6, 9, 5, 13]
  IO.println "OK"
