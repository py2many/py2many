def test_range():
    simple = list(range(0, 10))
    results = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    assert simple == results


def test_range_with_steps():
    with_steps = list(range(0, 10, 2))
    results = [0, 2, 4, 6, 8]
    assert with_steps == results


def test_range_with_negative_steps():
    with_steps = list(range(10, 0, -2))
    results = [10, 8, 6, 4, 2]
    assert with_steps == results
