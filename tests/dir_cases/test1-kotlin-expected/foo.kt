import bar.bar1
import baz.baz1

fun main(argv: Array<String>) {
    val x = bar1()
    val y = baz1()
    assert(x == 0)
    assert(y == "foo")
}
