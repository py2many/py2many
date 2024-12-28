

enum class Colors(
    val value: Int,
) {
    RED(0),
    GREEN(1),
    BLUE(2),
}

enum class Permissions(
    val value: Int,
) {
    R(1),
    W(2),
    X(16),
}

fun show() {
    val color_map = hashMapOf(Colors.RED to "red", Colors.GREEN to "green", Colors.BLUE to "blue")
    val a = Colors.GREEN
    if (a == Colors.GREEN) {
        println("green")
    } else {
        println("Not green")
    }
    val b = Permissions.R
    if (b == Permissions.R) {
        println("R")
    } else {
        println("Not R")
    }
    assert(color_map.size != 0)
}

fun main(argv: Array<String>) {
    show()
}
