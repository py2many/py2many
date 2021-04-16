
data class Rectangle(val height: Int, val length: Int) {
    fun is_square(): Boolean {
        return height == length
    }
}

fun show() {
    var r = Rectangle(1, 1)
    assert(r.is_square())
    r = Rectangle(1, 2)
    assert(!r.is_square())
    val h = r.height
    val l = r.length
    println("$h")
    println("$l")
}

fun main() {
    show()
}
