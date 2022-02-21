import kotlin.math.max
import kotlin.math.min
fun default_builtins() {
    val a = ""
    val b = false
    val c = 0
    assert(a == "")
    assert(b == false)
    assert(c == 0)
}

fun main(argv: Array<String>) {
    val a = max(1, 2)
    println("$a")
    val b = min(1, 2)
    println("$b")
}
