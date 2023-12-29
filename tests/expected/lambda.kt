

fun show() {
    var myfunc: (Int, Int) -> Int = { x, y -> (x + y) }
    if (true) {
        val __tmp1 = myfunc(1, 2)
        println("$__tmp1")
    }
}

fun main(argv: Array<String>) {
    show()
}
