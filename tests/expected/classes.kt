class Foo {
    fun bar(): Int {
        return baz()
    }

    fun baz(): Int {
        return 10
    }
}

fun main(argv: Array<String>) {
    val f = Foo()
    val b = f.bar()
    println("$b")
    assert(b == 10)
}
