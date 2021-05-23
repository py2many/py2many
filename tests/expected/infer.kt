fun foo() {
    val a = 10
    val b = a
    assert(b == 10)
    println("$b")
}

fun main(argv: Array<String>) {
    foo()
}
