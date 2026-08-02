"""Backend-agnostic specification markers for py2many.

Usage::

    from py2many.spec import CHECKER

    @dataclass
    class BankAccount:
        balance: int

        if CHECKER.invariant:
            balance >= 0

        def deposit(self, amount: int) -> "BankAccount":
            if CHECKER.pre:
                amount > 0
            if CHECKER.post:
                result.balance == self.balance + amount
            return BankAccount(self.balance + amount)


``CHECKER.pre`` / ``CHECKER.post`` / ``CHECKER.invariant`` evaluate to
``False`` at runtime, so the ``if`` blocks are compiled out by any Python
interpreter.  py2many backends (Lean, SMT, …) recognise the dotted access
and treat the block bodies as proof obligations.

Legacy flat names (``pre``, ``post``, ``invariant``) are also exported for
backward compatibility with the older ``py2many.smt`` module.
"""


def check(claim: bool):
    """Assert a linear-arithmetic claim about specific values.

    Python checks it at runtime; the Lean backend discharges it with ``omega``
    at compile time — the runnable analogue of an SMT ``check-sat`` + model.
    """
    assert claim


def prove(fn):
    """Assert that a boolean function holds for every boolean input.

    Python exhaustively evaluates the finite ``bool`` domain so the case is
    ordinary runnable code.  The Lean backend compiles it to ``by decide``.
    """
    import inspect
    from itertools import product

    n = len(inspect.signature(fn).parameters)
    assert all(fn(*combo) for combo in product((True, False), repeat=n))


# ── CHECKER namespace (preferred API) ─────────────────────────


class _Checker:
    """Sentinel object whose attributes are always ``False``.

    ``if CHECKER.pre:`` blocks are eliminated at runtime by the Python
    bytecode compiler (the condition is a compile-time constant ``False``)
    and recognised by py2many's AST pass as specification markers.
    """

    pre = False
    post = False
    invariant = False


CHECKER = _Checker()

# ── Legacy flat exports (kept for backward compat) ────────────

pre = CHECKER.pre
post = CHECKER.post
invariant = CHECKER.invariant
