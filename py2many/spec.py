"""Backend-agnostic specification markers for py2many.

Usage::

    from py2many.spec import CHECKER, result

    @dataclass
    class BankAccount:
        balance: int

        if CHECKER.invariant:
            balance >= 0

        def deposit(self, amount: int) -> "BankAccount":
            if CHECKER.pre:
                amount > 0
            self.balance += amount
            if CHECKER.post:
                result.balance == self.balance + amount
            return self


``CHECKER.pre`` / ``CHECKER.post`` / ``CHECKER.invariant`` evaluate to
``False`` at runtime, so the ``if`` blocks are compiled out by any Python
interpreter.  py2many backends (Lean, SMT, …) recognise the dotted access
and treat the block bodies as proof obligations.

Inside an ``if CHECKER.post:`` block, ``result`` names the return value
(Dafny-style) and other names refer to the pre-call state; the Lean backend
rewrites ``result`` to the subtype binder and emits the postcondition as a
constraint on the return type.  ``result`` is a no-op sentinel exported below,
so importing it keeps linters (F821) quiet without any ``noqa`` comments.

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


# ── Return-value name for postconditions ─────────────────────


class _Result:
    """No-op sentinel bound to the name ``result`` inside ``if CHECKER.post:`` blocks.

    ``result`` names the return value of the enclosing function.  The block is
    dead at runtime (``CHECKER.post`` is False), so this is never evaluated; it
    only exists so the name resolves for static analyzers (F821) and type
    checkers.  Attribute access yields ``None``, so block bodies stay harmless
    even if executed directly.
    """

    def __getattr__(self, name: str):
        return None


result = _Result()

# ── Legacy flat exports (kept for backward compat) ────────────

pre = CHECKER.pre
post = CHECKER.post
invariant = CHECKER.invariant
