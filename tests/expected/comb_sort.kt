import kotlin.math.floor
import kotlin.math.max

fun comb_sort(seq: Array<Int>): Array<Int> {
    var gap = seq.size
    var swap = true
    while (gap > 1 || swap) {
        gap = max(1, floor((gap.toDouble() / 1.25)).toInt())
        swap = false
        for (i in (0..(seq.size - gap) - 1)) {
            if (seq[i] > seq[(i + gap)]) {
                if (true) {
                    val (__tmp1, __tmp2) = Pair(seq[(i + gap)], seq[i])
                    seq[i] = __tmp1
                    seq[(i + gap)] = __tmp2
                }
                swap = true
            }
        }
    }
    return seq
}

fun main(argv: Array<String>) {
    var unsorted = arrayOf(14, 11, 19, 5, 16, 10, 19, 12, 5, 12)
    val expected = arrayOf(5, 5, 10, 11, 12, 12, 14, 16, 19, 19)
    assert(comb_sort(unsorted) == expected)
    println("OK")
}
