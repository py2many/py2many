val code_0 = 0
val code_1 = 1
val l_a = arrayOf(code_0, code_1)
val code_a = "a"
val code_b = "b"
val l_b = arrayOf(code_a, code_b)

fun main(argv: Array<String>) {
    for (i in l_a) {
        println("$i")
    }
    for (j in l_b) {
        println("$j")
    }
    if ("a" in arrayOf("a", "b")) {
        println("OK")
    }
}
