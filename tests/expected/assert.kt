fun compare_assert(a: Int, b: Int) {
    assert(a == b)
    assert(!(0 == 1))
}

fun main() {
    compare_assert(1, 1)
    println("OK")
}
