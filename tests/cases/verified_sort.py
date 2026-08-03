from dataclasses import dataclass
from typing import List

from py2many.spec import CHECKER, result
from py2many.theorem import by, lemma, theorem

# ── Class with invariant (CHECKER.invariant) ───────────────────


@dataclass
class BankAccount:
    balance: int

    if CHECKER.invariant:

        def invariant(cls):
            return cls.balance >= 0

    def deposit(self, amount: int) -> "BankAccount":
        if CHECKER.pre:
            amount > 0
        self.balance += amount
        if CHECKER.post:
            result.balance == self.balance + amount
        return self


# ── Function with precondition (CHECKER.pre) ───────────────────


def safe_sqrt(n: int) -> int:
    """Returns floor(sqrt(n)).  Requires n >= 0."""
    if CHECKER.pre:
        n >= 0
    i: int = 0
    while i * i <= n:
        i += 1
    return i - 1


# ── @lemma (decorator style still works) ───────────────────────


@lemma
@by("native_decide")
def sqrt_of_9() -> bool:
    return safe_sqrt(9) == 3


# ── Merge sort unchanged ──────────────────────────────────────


def merge(left: List[int], right: List[int]) -> List[int]:
    result: List[int] = []
    i: int = 0
    j: int = 0
    while i < len(left) and j < len(right):
        if left[i] <= right[j]:
            result.append(left[i])
            i += 1
        else:
            result.append(right[j])
            j += 1
    while i < len(left):
        result.append(left[i])
        i += 1
    while j < len(right):
        result.append(right[j])
        j += 1
    return result


def take(xs: List[int], n: int) -> List[int]:
    out: List[int] = []
    i: int = 0
    while i < n:
        out.append(xs[i])
        i += 1
    return out


def drop(xs: List[int], n: int) -> List[int]:
    out: List[int] = []
    i: int = n
    while i < len(xs):
        out.append(xs[i])
        i += 1
    return out


def sort_u64(arr: List[int]) -> List[int]:
    if len(arr) <= 1:
        return arr
    mid: int = len(arr) // 2
    left: List[int] = sort_u64(take(arr, mid))
    right: List[int] = sort_u64(drop(arr, mid))
    return merge(left, right)


@by("native_decide")
@theorem
def concrete_example() -> bool:
    return sort_u64([3, 1, 4, 1, 5, 9, 2, 6]) == [1, 1, 2, 3, 4, 5, 6, 9]


if __name__ == "__main__":
    acct = BankAccount(10)
    print(acct.balance)
