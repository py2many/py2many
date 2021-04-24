
fun show() {
    var myfunc = { x, y -> (x + y) }
    if (true) {
        val __tmp1 = myfunc(1, 2)
        println("$__tmp1")
    } 
}

fun main() {
    show()
}
