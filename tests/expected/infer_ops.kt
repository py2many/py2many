
fun foo() {
    val a = 10
    val b = 20
    val c1 = (a + b)
    val c2 = (a - b)
    val c3 = (a * b)
    val c4 = (a / b)
    val c5 = -(a)
    val d = 2.0
    val e1 = (a + d)
    val e2 = (a - d)
    val e3 = (a * d)
    val e4 = (a / d)
    val f = -3.0
    val g = -(a)
}

fun add1(x: Byte, y: Byte): Short {
    return (x + y)
}

fun add2(x: Short, y: Short): Int {
    return (x + y)
}

fun add3(x: Int, y: Int): Long {
    return (x + y)
}

fun add4(x: Long, y: Long): Long {
    return (x + y)
}

fun add5(x: UByte, y: UByte): UShort {
    return (x + y)
}

fun add6(x: UShort, y: UShort): UInt {
    return (x + y)
}

fun add7(x: UInt, y: UInt): ULong {
    return (x + y)
}

fun add8(x: ULong, y: ULong): ULong {
    return (x + y)
}

fun add9(x: Byte, y: UShort): UInt {
    return (x + y)
}

fun sub(x: Byte, y: Byte): Byte {
    return (x - y)
}

fun mul(x: Byte, y: Byte): Short {
    return (x * y)
}

fun fadd(x: Byte, y: Double): Double {
    return (x + y)
}

fun show() {
    val rv = fadd(6, 6.0)
    assert(rv == 12)
    println("$rv")
}

fun main() {
    foo()
    show()
}
