
enum class Colors(val value: String) {
    RED("red"),
    GREEN("green"),
    BLUE("blue"),
}
fun show() {
    val color_map = hashMapOf(Colors.RED to "1", Colors.GREEN to "2", Colors.BLUE to "3")
    val a = Colors.GREEN
    if (a == Colors.GREEN) {
        println("green")
    } else {
        println("Not green")
    } 
}

fun main() {
    show()
}
