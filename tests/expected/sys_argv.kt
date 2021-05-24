

fun main(argv: Array<String>) {
    var a: Array<String> = (arrayOf("") + argv)
    var cmd: String = a[0]
    assert("sys_argv" in cmd)
    if (a.size > 1) {
        if (true) {
            val __tmp1 = a[1]
            println("$__tmp1")
        }
    } else {
        println("OK")
    }
}
