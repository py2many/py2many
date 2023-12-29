

fun bubble_sort(seq: Array<Int>): Array<Int> {
    val L = seq.size
    for (__tmp1 in (0..L - 1)) {
        for (n in (1..L - 1)) {
            if (seq[n] < seq[(n.toInt() - 1)]) {
                if (true) {
                    val (__tmp1, __tmp2) = Pair(seq[n], seq[(n.toInt() - 1)])
                    seq[(n.toInt() - 1)] = __tmp1
                    seq[n] = __tmp2
                }
            }
        }
    }
    return seq
}

fun main(argv: Array<String>) {
    var unsorted = arrayOf(14, 11, 19, 5, 16, 10, 19, 12, 5, 12)
    val expected = arrayOf(5, 5, 10, 11, 12, 12, 14, 16, 19, 19)
    assert(bubble_sort(unsorted) == expected)
    println("OK")
}
