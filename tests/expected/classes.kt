class Foo {
    fun bar(): Int = baz()

    fun baz(): Int = 10
}

fun main(argv: Array<String>) {
    val f = Foo()
    val b = f.bar()
    println("$b")
    assert(b == 10)
}
