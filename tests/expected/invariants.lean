set_option linter.unusedVariables false

structure BankAccount where
  balance : Nat
  inv_balance : balance ≥ 0

def BankAccount.deposit (self : BankAccount) (amount : Nat) (pre : amount > 0) : BankAccount :=
  { balance := (self.balance + amount), inv_balance := by have h0 := self.inv_balance; omega : BankAccount }

def main_func : IO Unit := do
  let acct := { balance := 10, inv_balance := by omega : BankAccount }
  let acct2 := (acct.deposit 5 (by omega))
  IO.println (toString acct2.balance)

def main : IO Unit := do
  main_func
