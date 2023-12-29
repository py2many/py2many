fun show() {
    val a = 1
    val b = if (a in arrayOf(2, 3)) 2 else 3
    println("$b")
}

fun main(argv: Array<String>) {
    show()
}
