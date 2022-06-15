function foo()
    a = 10
    b = a
    @assert(b == 10)
end

function fibonacci(n)::Int64
    if n == 0
        return 0
    elseif n == 1
        return 1
    else
        return fibonacci(n - 2) + fibonacci(n - 1)
    end
end

function mul_list()
    a::Vector = []
    for i = 0:4
        push!(a, i)
    end
    return repeat(a, 2)
end

function combinations(array)::Vector
    result = []
    for x in array
        for y in array
            push!(result, (x, y))
        end
    end
    return result
end

function mul_recvd_list(a::Vector)
    for i = 0:length(a)-1
        push!(a, i)
    end
    return repeat(a, 2)
end

function plus_test(x, y)::Any
    return x + y
end

function plus_test(x::String, y::String)::String
    return x * y
end

if abspath(PROGRAM_FILE) == @__FILE__
    foo()
    @assert(fibonacci(10) == 55)
    @assert((repeat("test", fibonacci(3))) == "testtest")
    a = []
    a_mul = mul_recvd_list(a)
    @assert(a_mul == [])
    x = "ss"
    y = "zz"
    res = plus_test(x, y)
    @assert(res == "sszz")
    println("OK")
end
