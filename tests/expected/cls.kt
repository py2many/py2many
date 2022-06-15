class Foo {

    fun bar(): String {
        return "a"
    }
}

fun main(argv: Array<String>) {
    val f = Foo()
    val b = f.bar()
    println("$b")
}
