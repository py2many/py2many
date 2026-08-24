def test() raises -> Int:
    var a: List[Int] = List([1, 2, 3])
    return a[1]


def main() raises:
    var b = test()
    assert b == 2
    print("OK")
