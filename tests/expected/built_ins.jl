function default_builtins()
    a = String()
    b = false
    c = zero(Int)
    d = zero(Float64)
    @assert(a == "")
    @assert(b == false)
    @assert(c == 0)
    @assert(d == 0.0)
end

function main()
    a = max(1, 2)
    println(a)
    b = min(1, 2)
    println(b)
    c = Int(floor(min(1.0, 2.0)))
    println(c)
end

main()
