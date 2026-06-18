from std.testing import assert_true


fn default_builtins() raises:
    var a = ""
    var b = False
    var c = 0
    var d = 0.0
    assert_true(a == "")
    assert_true(b == False)
    assert_true(c == 0)
    assert_true(d == 0.0)


fn main():
    var a = max(1, 2)
    print(a)
    var b = min(1, 2)
    print(b)
    var c = Int(min(1.0, 2.0))
    print(c)
