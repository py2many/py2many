def foo() raises:
    var a = 10
    var b = 20
    var _ = a + b
    var _ = a - b
    var _ = a * b
    var _ = a / b
    var _ = -(a)
    var d = 2.0
    var _ = Float64(a) + d
    var _ = Float64(a) - d
    var _ = Float64(a) * d
    var _ = Float64(a) / d
    var _ = -3.0
    var _ = -(a)


def add1(x: Int8, y: Int8) raises -> Int16:
    return Int16((x + y))


def add2(x: Int16, y: Int16) raises -> Int32:
    return Int32((x + y))


def add3(x: Int32, y: Int32) raises -> Int64:
    return Int64((x + y))


def add4(x: Int64, y: Int64) raises -> Int64:
    return x + y


def add5(x: UInt8, y: UInt8) raises -> UInt16:
    return UInt16((x + y))


def add6(x: UInt16, y: UInt16) raises -> UInt32:
    return UInt32((x + y))


def add7(x: UInt32, y: UInt32) raises -> UInt64:
    return UInt64((x + y))


def add8(x: UInt64, y: UInt64) raises -> UInt64:
    return x + y


def add9(x: Int8, y: UInt16) raises -> UInt32:
    return UInt32((Int32(x) + Int32(y)))


def sub(x: Int8, y: Int8) raises -> Int8:
    return x - y


def mul(x: Int8, y: Int8) raises -> Int16:
    return Int16((x * y))


def fadd1(x: Int8, y: Float64) raises -> Float64:
    return Float64(x) + y


def show() raises:
    assert fadd1(6, 6.0) == 12
    print("OK")


def main() raises:
    foo()
    show()
