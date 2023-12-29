val code_0 = 0
val code_1 = 1
val code_a = "a"
val code_b = "b"
val l_b = setOf(code_a)
val l_c = hashMapOf(code_b to code_0)

fun main(argv: Array<String>) {
    assert("a" in l_b)
    println("OK")
}
