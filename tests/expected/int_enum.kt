
class Colors {
    val RED: ST0
    val GREEN: ST1
    val BLUE: ST2

    val RED = auto()
    val GREEN = auto()
    val BLUE = auto()
}

class Permissions {
    val R: ST0
    val W: ST1
    val X: ST2

    val R = 1
    val W = 2
    val X = 16
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

fun main() {
    show()
}
