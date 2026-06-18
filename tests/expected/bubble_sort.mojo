from std.testing import assert_true


fn bubble_sort(var seq: List[Int]) -> List[Int]:
    var L = len(seq)
    for _ in range(L):
        for n in range(1, L):
            if seq[n] < seq[(n - 1)]:
                (seq[(n - 1)], seq[n]) = (seq[n], seq[(n - 1)])

    return seq^


fn main() raises:
    var unsorted = [14, 11, 19, 5, 16, 10, 19, 12, 5, 12]
    var expected = [5, 5, 10, 11, 12, 12, 14, 16, 19, 19]
    assert_true(bubble_sort(unsorted^) == expected)
    print("OK")
