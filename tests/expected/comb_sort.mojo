from std.math import floor


def comb_sort(var seq: List[Int]) raises -> List[Int]:
    var gap = len(seq)
    var swap = True
    while gap > 1 or swap:
        gap = max(1, Int(floor(Float64((Float64(gap) / 1.25)))))
        swap = False
        for i in range((len(seq) - gap)):
            if seq[i] > seq[(i + gap)]:
                var tmp1_0 = seq[(i + gap)]
                var tmp1_1 = seq[i]
                seq[i] = tmp1_0
                seq[(i + gap)] = tmp1_1
                swap = True

    return seq^


def main() raises:
    var unsorted = List([14, 11, 19, 5, 16, 10, 19, 12, 5, 12])
    var expected = List([5, 5, 10, 11, 12, 12, 14, 16, 19, 19])
    assert comb_sort(unsorted^) == expected
    print("OK")
