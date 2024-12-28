

fun foo() {
    val a = 10
    val b = 20
    val _c1 = (a + b)
    val _c2 = (a - b)
    val _c3 = (a * b)
    val _c4 = (a / b)
    val _c5 = -(a)
    val d = 2.0
    val _e1 = (a.toDouble() + d)
    val _e2 = (a.toDouble() - d)
    val _e3 = (a.toDouble() * d)
    val _e4 = (a.toDouble() / d)
    val _f = -3.0
    val _g = -(a)
}

fun add1(
    x: Byte,
    y: Byte,
): Short = (x + y) as Short

fun add2(
    x: Short,
    y: Short,
): Int = (x + y)

fun add3(
    x: Int,
    y: Int,
): Long = (x + y) as Long

fun add4(
    x: Long,
    y: Long,
): Long = (x + y)

fun add5(
    x: UByte,
    y: UByte,
): UShort = (x + y) as UShort

fun add6(
    x: UShort,
    y: UShort,
): UInt = (x + y)

fun add7(
    x: UInt,
    y: UInt,
): ULong = (x + y) as ULong

fun add8(
    x: ULong,
    y: ULong,
): ULong = (x + y)

fun add9(
    x: Byte,
    y: UShort,
): UInt = (x.toUShort() + y)

fun sub(
    x: Byte,
    y: Byte,
): Byte = (x - y) as Byte

fun mul(
    x: Byte,
    y: Byte,
): Short = (x * y) as Short

fun fadd1(
    x: Byte,
    y: Double,
): Double = (x.toDouble() + y)

fun show() {
    assert(fadd1(6, 6.0) == 12.toDouble())
    println("OK")
}

fun main(argv: Array<String>) {
    foo()
    show()
}
