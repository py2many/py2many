from transpiler import transpile


def test_declare():
    python = "x = 3"
    cpp = transpile(python)
    assert cpp == "auto x = 3;"


def test_assign():
    python = "x = 3; x = 1"
    cpp = transpile(python)
    assert cpp == "auto x = 3;\nx = 1;"
