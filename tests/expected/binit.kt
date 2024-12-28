

fun bisect_right(
    data_: Array<Int>,
    item: Int,
): Int {
    var low = 0
    var high: Int = data_.size.toInt()
    while (low < high) {
        val middle = ((low + high) / 2).toInt()
        if (item < data_[middle]) {
            high = middle
        } else {
            low = (middle + 1)
        }
    }
    return low
}

fun bin_it(
    limits: Array<Int>,
    data_: Array<Int>,
): Array<Int> {
    var bins = arrayOf(0)
    for (_x in limits) {
        bins += 0
    }
    for (d in data_) {
        bins[bisect_right(limits, d)] += 1
    }
    return bins
}

fun main(argv: Array<String>) {
    val limits = arrayOf(23, 37, 43, 53, 67, 83)
    val data_ = arrayOf(95, 21, 94, 12, 99, 4, 70, 75, 83, 93, 52, 80, 57, 5, 53, 86, 65, 17, 92, 83, 71, 61, 54, 58, 47, 16, 8, 9, 32, 84, 7, 87, 46, 19, 30, 37, 96, 6, 98, 40, 79, 97, 45, 64, 60, 29, 49, 36, 43, 55)
    assert(bin_it(limits, data_) == arrayOf(11, 4, 2, 6, 9, 5, 13))
    println("OK")
}
