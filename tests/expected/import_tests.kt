

fun test(): Int {
    var a: Array<Int> = arrayOf(1, 2, 3)
    return a[1]
}

fun main(argv: Array<String>) {
    val b = test()
    assert(b == 2)
    println("OK")
}
