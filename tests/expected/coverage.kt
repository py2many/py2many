
fun indexing(): Int {
    var sum = 0
    var a: Array<Int> = arrayOf()
    for (i in (0..10 - 1)) {
        a += i
        sum += a[i]
    }
    return sum
}

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
    val sum1 = indexing()
    println("$sum1")
    val a5 = arrayOf(1, 2, 3)
    if (true) {
        val __tmp1 = a5.size
        println("$__tmp1")
    }
    var a9: Array<String> = arrayOf("a", "b", "c", "d")
    if (true) {
        val __tmp2 = a9.size
        println("$__tmp2")
    }
    if (1 != null) {
        println("World is sane")
    } 
}

fun main() {
    show()
}
