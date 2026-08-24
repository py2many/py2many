def bubble_sort(var seq: List[Int]) raises -> List[Int]:
    var L = len(seq)
    for _ in range(L):
        for n in range(1, L):
            if seq[n] < seq[(n - 1)]:
                var tmp1_0 = seq[n]
                var tmp1_1 = seq[(n - 1)]
                seq[(n - 1)] = tmp1_0
                seq[n] = tmp1_1

    return seq^


def main() raises:
    var unsorted = List([14, 11, 19, 5, 16, 10, 19, 12, 5, 12])
    var expected = List([5, 5, 10, 11, 12, 12, 14, 16, 19, 19])
    assert bubble_sort(unsorted^) == expected
    print("OK")
