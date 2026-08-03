fun show() {
    var my_list = arrayOf(1, 2, 3, 4, 5)
// del unimplemented on line 7:4
    if (true) {
        val __tmp1 = my_list.size
        println("$__tmp1")
    }
    var my_dict = hashMapOf("a" to 1, "b" to 2, "c" to 3)
// del unimplemented on line 12:4
    if (true) {
        val __tmp2 = my_dict.size
        println("$__tmp2")
    }
}

fun main(argv: Array<String>) {
    show()
}
