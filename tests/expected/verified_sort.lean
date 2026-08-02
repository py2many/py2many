set_option linter.unusedVariables false

structure BankAccount where
  balance : Nat
  inv_balance : balance ≥ 0

def BankAccount.deposit (self : BankAccount) (amount : Nat) (pre : amount > 0) : BankAccount :=
  { balance := (self.balance + amount), inv_balance := by have h0 := self.inv_balance; omega : BankAccount }

def safe_sqrt (n : Nat) (pre : n ≥ 0) : Nat :=
  Id.run
    (do
      let mut i : Nat := 0
      while (i * i) ≤ n do
        i := i + 1
      return (i - 1))

theorem sqrt_of_9 : ((safe_sqrt 9 (by omega)) == 3) = true := by native_decide

def merge (left : List Nat) (right : List Nat) : List Nat :=
  Id.run
    (do
      let mut result : List Nat := []
      let mut i : Nat := 0
      let mut j : Nat := 0
      while (i < (left).length && j < (right).length) do
        if left[i]! ≤ right[j]! then
          result := result ++ [left[i]!]
          i := i + 1
        else
          result := result ++ [right[j]!]
          j := j + 1
      while i < (left).length do
        result := result ++ [left[i]!]
        i := i + 1
      while j < (right).length do
        result := result ++ [right[j]!]
        j := j + 1
      return result)

def take (xs : List Nat) (n : Nat) : List Nat :=
  Id.run
    (do
      let mut out : List Nat := []
      let mut i : Nat := 0
      while i < n do
        out := out ++ [xs[i]!]
        i := i + 1
      return out)

def drop (xs : List Nat) (n : Nat) : List Nat :=
  Id.run
    (do
      let mut out : List Nat := []
      let mut i : Nat := n
      while i < (xs).length do
        out := out ++ [xs[i]!]
        i := i + 1
      return out)

partial def sort_u64 (arr : List Nat) : List Nat :=
  Id.run
    (do
      if (arr).length ≤ 1 then
        return arr
      let mid : Nat := ((arr).length / 2)
      let left : List Nat := (sort_u64 (take arr mid))
      let right : List Nat := (sort_u64 (drop arr mid))
      return (merge left right))

theorem concrete_example : ((sort_u64 [3, 1, 4, 1, 5, 9, 2, 6]) == [1, 1, 2, 3, 4, 5, 6, 9]) = true := by native_decide

def main : IO Unit := do
  let acct := { balance := 10, inv_balance := by omega : BankAccount }
  IO.println "OK"
