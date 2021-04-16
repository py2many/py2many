fun fib(i: Int): Int {
    if (i == 0 || i == 1) {
        return 1
    }
    return (fib((i - 1)) + fib((i - 2)))
}

fun main() {
    val rv = fib(5)
    println("$rv")
}
