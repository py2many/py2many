fun fib(i: Int): Int {
    if (i == 0 || i == 1) {
        return 1
    }
    return (fib((i - 1)) + fib((i - 2)))
}

fun main(argv: Array<String>) {
    if (true) {
        val __tmp1 = fib(5)
        println("$__tmp1")
    }
}
