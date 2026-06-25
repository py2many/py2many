def check(claim: bool):
    """Assert a linear-arithmetic claim about specific values.

    Python checks it at runtime; the Lean backend discharges it with ``omega``
    at compile time -- the runnable analogue of an SMT model satisfying its
    constraints (``check-sat`` + ``get-value``).
    """
    assert claim


def prove(fn):
    """Assert that a boolean function holds for every boolean input.

    In Python this exhaustively evaluates the finite ``bool`` domain so the
    case is ordinary, runnable code.  The Lean backend recognises the call and
    compiles it to ``by decide`` -- a complete decision procedure that proves
    the same property for all inputs at compile time (the analogue of an SMT
    ``check-sat`` returning ``unsat``).
    """
    import inspect
    from itertools import product

    n = len(inspect.signature(fn).parameters)
    assert all(fn(*combo) for combo in product((True, False), repeat=n))


# Dummy interfaces
def check_sat(): ...


def get_model(*args): ...


def get_value(*args): ...


def default_value(type_):
    try:
        return type_()
    except TypeError:
        return None


class Array:
    def __class_getitem__(cls, _):
        return cls


# So the pre/post conditions and invariants are compiled out
pre = False
post = False
invariant = False
