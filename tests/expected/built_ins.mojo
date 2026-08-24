def default_builtins() raises:
    var a = ""
    var b = False
    var c = 0
    var d = 0.0
    assert a == ""
    assert b == False
    assert c == 0
    assert d == 0.0


def main() raises:
    var a = max(1, 2)
    print(a)
    var b = min(1, 2)
    print(b)
    var c = Int(min(1.0, 2.0))
    print(c)
