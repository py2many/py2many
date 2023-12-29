fun compare_assert(
    a: Int,
    b: Int,
) {
    assert(a == b)
    assert(!(0 == 1))
}

fun main(argv: Array<String>) {
    assert(true)
    assert(!(false))
    compare_assert(1, 1)
    assert(true)
    assert(true)
    println("OK")
}
