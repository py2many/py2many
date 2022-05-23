
function inline_pass()
    #= pass =#
end

function inline_ellipsis()
end

function indexing()::Int64
    sum = 0
    a::Vector{Int64} = []
    for i = 0:9
        push!(a, i)
        sum += a[i+1]
    end
    return sum
end

function infer_bool(code::Int64)::Bool
    return code ∈ [1, 2, 4]
end

function show()
    a1 = 10
    b1 = 15
    b2 = 15
    @assert(b1 == 15)
    @assert(b2 == 15)
    b9 = 2
    b10 = 2
    @assert(b9 == b10)
    a2::Float64 = 2.1
    @assert(a2 == 2.1)
    res = []
    for i = 0:9
        push!(res, i)
    end
    for i = 0:2:9
        push!(res, i)
    end
    for i = 1:9
        push!(res, i)
    end
    @assert(res == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 2, 4, 6, 8, 1, 2, 3, 4, 5, 6, 7, 8, 9])
    a3 = -(a1)
    @assert(a3 == -10)
    a4 = a3 + a1
    @assert(a4 == 0)
    t1 = a1 > 5 ? (10) : (5)
    @assert(t1 == 10)
    sum1 = indexing()
    @assert(sum1 == 45)
    a5 = [1, 2, 3]
    println(length(a5))
    a9::Vector{String} = ["a", "b", "c", "d"]
    @assert(length(a9) == 4)
    @assert(a9 == ["a", "b", "c", "d"])
    a6 = Set([1, 2, 3, 4])
    i = (x for x in a6)
    @assert(length(a6) == 4)
    @assert(next(i, nothing) == 1)
    @assert(next(i, nothing) == 2)
    @assert(next(i, nothing) == 3)
    @assert(next(i, nothing) == 4)
    @assert(next(i, nothing) === nothing)
    a7 = Dict("a" => 1, "b" => 2)
    @assert(length(a7) == 2)
    @assert(a7["a"] == 1)
    @assert(a7["b"] == 2)
    a8 = true
    a9 = false
    @assert(a8 == true)
    @assert(a9 == false)
    if true
        a1 += 1
    end
    @assert(a1 == 11)
    @assert(Bool(1))
    @assert(infer_bool(1))
    @assert(1 != 2 != 3)
    if a8
        println("true")
    elseif a4 > 0
        println("never get here")
    end
    if a1 == 11
        println("false")
    else
        println("true")
    end
    if 1 != nothing
        println("World is sane")
    end
    println(true ? ("True") : ("False"))
    if true
        println("true")
    end
    inline_pass()
    s = "1    2"
    @assert(s == "1    2")
    _escape_quotes = " foo \"bar\" baz "
    @assert(findfirst("bbc", "aaabbccc") != Nothing)
    2
    _c1, _c2 = (1, 3)
    (_c3, _, _c4) = [1, 2, 3]
    @assert(_c1 == 1)
    @assert(_c2 == 3)
    @assert(_c3 == 1)
    @assert(_c4 == 3)
end

if abspath(PROGRAM_FILE) == @__FILE__
    show()
end
