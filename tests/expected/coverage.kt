fun show() {
    val a1 = 10
    var a2: Double = 2.1
    println("$a2")
    for (i in (0..10 - 1)) {
        println("$i")
    }
    for (i in (0..10 - 1 step 2)) {
        println("$i")
    }
    val a3 = -(a1)
    val a4 = (a3 + a1)
    println("$a4")
}

fun main() {
    show()
}
