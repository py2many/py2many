
fun bisect_right(data_: Array<Int>, item: Int): Int {
    var low = 0
    var high = data_.size
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

fun bin_it(limits: Array<Int>, data_: Array<Int>): Array<Int> {
    var bins = arrayOf(0)
    for (x in limits) {
        bins.append(0)
    }
    for (d in data_) {
        bins[bisect_right(limits, d)] += 1
    }
    return bins
}
