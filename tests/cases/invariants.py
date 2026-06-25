from dataclasses import dataclass

from py2many.smt import invariant
from py2many.smt import pre as smt_pre


@dataclass
class BankAccount:
    balance: int

    if invariant:
        balance >= 0

    def deposit(self, amount: int) -> "BankAccount":
        if smt_pre:
            amount > 0
        return BankAccount(self.balance + amount)


def main():
    acct = BankAccount(10)
    acct2 = acct.deposit(5)
    print(acct2.balance)


if __name__ == "__main__":
    main()
