class Foo {
    fun bar(): String = "a"
}

fun main(argv: Array<String>) {
    val f = Foo()
    val b = f.bar()
    println("$b")
}
