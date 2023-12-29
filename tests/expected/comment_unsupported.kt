fun do_unsupported() {
    val a = 1
// dict comprehension ((key.toInt() + 1), (value.toInt() + 1)) unimplemented on line 9:4
    val b = (a != 0)
    if (true) {
        val __tmp1 = if (b) "True" else "False"
        println("$__tmp1")
    }
}

fun main(argv: Array<String>) {
    do_unsupported()
}
