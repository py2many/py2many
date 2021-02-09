
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

function add1(x::c_int8, y::c_int8)::c_int16
    return (x + y)
end

function add2(x::c_int16, y::c_int16)::c_int32
    return (x + y)
end

function add3(x::c_int32, y::c_int32)::c_int64
    return (x + y)
end

function add4(x::c_int64, y::c_int64)::c_int64
    return (x + y)
end

function add5(x::c_uint8, y::c_uint8)::c_uint16
    return (x + y)
end

function add6(x::c_uint16, y::c_uint16)::c_uint32
    return (x + y)
end

function add7(x::c_uint32, y::c_uint32)::c_uint64
    return (x + y)
end

function add8(x::c_uint64, y::c_uint64)::c_uint64
    return (x + y)
end

function add9(x::c_int8, y::c_uint16)::c_uint32
    return (x + y)
end

function sub(x::c_int8, y::c_int8)::c_int8
    return (x - y)
end

function mul(x::c_int8, y::c_int8)::c_int16
    return (x * y)
end

function fadd(x::c_int8, y::Float64)::Float64
    return (x + y)
end
