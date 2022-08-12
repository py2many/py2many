
function foo()
    a = 10
    b = 20
    _c1 = a + b
    _c2 = a - b
    _c3 = a * b
    _c4 = a / b
    _c5 = -a
    d = 2.0
    _e1 = a + d
    _e2 = a - d
    _e3 = a * d
    _e4 = a / d
    _f = -3.0
    _g = -a
end

function add1(x::Cuint, y::Cuint)::Cshort
    return x + y
end

function add2(x::Cshort, y::Cshort)::Clong
    return x + y
end

function add3(x::Clong, y::Clong)::Cssize_t
    return x + y
end

function add4(x::Cssize_t, y::Cssize_t)::Cssize_t
    return x + y
end

function add5(x::Cuint, y::Cuint)::Cushort
    return x + y
end

function add6(x::Cushort, y::Cushort)::Culong
    return x + y
end

function add7(x::Culong, y::Culong)::Csize_t
    return x + y
end

function add8(x::Csize_t, y::Csize_t)::Csize_t
    return x + y
end

function add9(x::Cuint, y::Cushort)::Culong
    return x + y
end

function sub(x::Cuint, y::Cuint)::Cuint
    return x - y
end

function mul(x::Cuint, y::Cuint)::Cshort
    return x * y
end

function fadd1(x::Cuint, y::Float64)
    return x + y
end

function show()
    @assert(fadd1(convert(Cuint, 6), 6.0) == 12)
    @assert(add1(convert(Cuint, 127), convert(Cuint, 1)) == 128)
    @assert(add2(convert(Cshort, 32767), convert(Cshort, 1)) == 32768)
    @assert(add3(convert(Clong, 2147483647), convert(Clong, 1)) == 2147483648)
    @assert(
        add4(convert(Cssize_t, 9223372036854775807), convert(Cssize_t, 1)) ==
        9223372036854775808
    )
    println("OK")
end

if abspath(PROGRAM_FILE) == @__FILE__
    foo()
    show()
end
