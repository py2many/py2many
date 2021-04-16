
function foo()
    a = 10
    b = 20
    c1 = (a + b)
    c2 = (a - b)
    c3 = (a * b)
    c4 = (a / b)
    c5 = -(a)
    d = 2.0
    e1 = (a + d)
    e2 = (a - d)
    e3 = (a * d)
    e4 = (a / d)
    f = -3.0
    g = -(a)
end

function add1(x::Int8, y::Int8)::Int16
    return (x + y)
end

function add2(x::Int16, y::Int16)::Int32
    return (x + y)
end

function add3(x::Int32, y::Int32)::Int64
    return (x + y)
end

function add4(x::Int64, y::Int64)::Int64
    return (x + y)
end

function add5(x::UInt8, y::UInt8)::UInt16
    return (x + y)
end

function add6(x::UInt16, y::UInt16)::UInt32
    return (x + y)
end

function add7(x::UInt32, y::UInt32)::UInt64
    return (x + y)
end

function add8(x::UInt64, y::UInt64)::UInt64
    return (x + y)
end

function add9(x::Int8, y::UInt16)::UInt32
    return (x + y)
end

function sub(x::Int8, y::Int8)::Int8
    return (x - y)
end

function mul(x::Int8, y::Int8)::Int16
    return (x * y)
end

function fadd(x::Int8, y::Float64)::Float64
    return (x + y)
end

function show()
    rv = fadd(6, 6.0)
    @assert(rv == 12)
    println(join([rv], " "))
end

function main()
    foo()
    show()
end
