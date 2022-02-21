fun show() {
    println("b")
    println("2 b")
    var a: Double = 2.1
    println("$a")
    val b = 2.1
    println("$b")
    val c = true
    if (true) {
        val __tmp1 = if (c) "True" else "False"
        println("$__tmp1")
    }
}

fun main(argv: Array<String>) {
    show()
}
