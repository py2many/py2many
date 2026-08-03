

fun equation(
    x: Int,
    y: Int,
): Boolean = x > 2 && y < 10 && (x + (2 * y)) == 7

fun fequation(z: Double): Boolean {
    val diff = ((7.0 * z) - 1.0)
    return -0.001 < diff && diff < 0.001
}

fun main_func() {
    val x = 7
    val y = 0
    val z = 0.142857
    check(equation(x, y))
    check(fequation(z))
    println("$x")
    println("$y")
    println("$z")
}

fun main(argv: Array<String>) {
    main_func()
}
