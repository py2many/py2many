from std.testing import assert_true
from std.math import floor


fn comb_sort(var seq: List[Int]) -> List[Int]:
    var gap = len(seq)
    var swap = True
    while gap > 1 or swap:
        gap = max(1, Int(floor((gap / 1.25))))
        swap = False
        for i in range((len(seq) - gap)):
            if seq[i] > seq[(i + gap)]:
                (seq[i], seq[(i + gap)]) = (seq[(i + gap)], seq[i])
                swap = True

    return seq^


fn main() raises:
    var unsorted = [14, 11, 19, 5, 16, 10, 19, 12, 5, 12]
    var expected = [5, 5, 10, 11, 12, 12, 14, 16, 19, 19]
    assert_true(comb_sort(unsorted^) == expected)
    print("OK")
