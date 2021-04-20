
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
}

fun main() {
    show()
}
