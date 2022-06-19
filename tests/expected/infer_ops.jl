
function foo()
    a = 10
    b = 20
    _c1 = a + b
    _c2 = a - b
    _c3 = a * b
    _c4 = a / b
    _c5 = -(a)
    d = 2.0
    _e1 = a + d
    _e2 = a - d
    _e3 = a * d
    _e4 = a / d
    _f = -3.0
    _g = -(a)
end

function add1(x::Int8, y::Int8)::Int16
    return x + y
end

function add2(x::Int16, y::Int16)::Int32
    return x + y
end

function add3(x::Int32, y::Int32)::Int64
    return x + y
end

function add4(x::Int64, y::Int64)::Int64
    return x + y
end

function add5(x::UInt8, y::UInt8)::UInt16
    return x + y
end

function add6(x::UInt16, y::UInt16)::UInt32
    return x + y
end

function add7(x::UInt32, y::UInt32)::UInt64
    return x + y
end

function add8(x::UInt64, y::UInt64)::UInt64
    return x + y
end

function add9(x::Int8, y::UInt16)::UInt32
    return x + y
end

function sub(x::Int8, y::Int8)::Int8
    return x - y
end

function mul(x::Int8, y::Int8)::Int16
    return x * y
end

function fadd1(x::Int8, y::Float64)::Float64
    return x + y
end

function show()
    @assert(fadd1(convert(Int8, 6), 6.0) == 12)
    println(join(["OK"], " "))
end

function main()
    foo()
    show()
end

main()
