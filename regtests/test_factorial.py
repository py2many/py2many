def factorial(num):
    if num <= 1:
        return num
    return factorial(num-1) * num


def test_factorial():
    assert factorial(1) == 1
    assert factorial(2) == 2
    assert factorial(3) == 6
    assert factorial(10) == 3628800
