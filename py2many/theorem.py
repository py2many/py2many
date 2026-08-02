"""Transpiler-only decorator markers for py2many.

These decorators are recognised by py2many's AST pass and are no-ops at
Python runtime.  Import them so your source file stays executable::

    from py2many.theorem import theorem, lemma, by
"""


def theorem(fn):
    """Marker for py2many: emit ``theorem`` instead of ``def``."""
    return fn


def lemma(fn):
    """Marker for py2many: emit ``theorem`` (alias for ``lemma``)."""
    return fn


def by(tactic: str):
    """Marker for py2many: use *tactic* as the proof block.

    At runtime this is a no-op decorator that returns the function unchanged.
    """

    def decorator(fn):
        return fn

    return decorator
