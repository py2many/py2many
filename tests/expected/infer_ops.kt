
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

fun add1(x: c_int8, y: c_int8): c_int16 {
    return (x + y)
}

fun add2(x: c_int16, y: c_int16): c_int32 {
    return (x + y)
}

fun add3(x: c_int32, y: c_int32): c_int64 {
    return (x + y)
}

fun add4(x: c_int64, y: c_int64): c_int64 {
    return (x + y)
}

fun add5(x: c_uint8, y: c_uint8): c_uint16 {
    return (x + y)
}

fun add6(x: c_uint16, y: c_uint16): c_uint32 {
    return (x + y)
}

fun add7(x: c_uint32, y: c_uint32): c_uint64 {
    return (x + y)
}

fun add8(x: c_uint64, y: c_uint64): c_uint64 {
    return (x + y)
}

fun add9(x: c_int8, y: c_uint16): c_uint32 {
    return (x + y)
}

fun sub(x: c_int8, y: c_int8): c_int8 {
    return (x - y)
}

fun mul(x: c_int8, y: c_int8): c_int16 {
    return (x * y)
}

fun fadd(x: c_int8, y: Double): Double {
    return (x + y)
}
