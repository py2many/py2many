// This file implements a rectangle class

data class Rectangle(
    val height: Int,
    val length: Int,
) {
    fun is_square(): Boolean = height == length
}

fun show() {
    var r = Rectangle(1, 1)
    assert(r.is_square())
    r = Rectangle(1, 2)
    assert(!(r.is_square()))
    if (true) {
        val __tmp1 = r.height
        println("$__tmp1")
    }
    if (true) {
        val __tmp2 = r.length
        println("$__tmp2")
    }
}

fun main(argv: Array<String>) {
    show()
}
