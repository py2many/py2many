function default_builtins()
    a = ""
    b = false
    c = 0
    d = float()
    @assert(a == "")
    @assert(b == false)
    @assert(c == 0)
    @assert(d == 0.0)
end

function main()
    a = max(1, 2)
    println(join([a], " "))
    b = min(1, 2)
    println(join([b], " "))
    c = Int64(floor(min(1.0, 2.0)))
    println(join([c], " "))
end

main()
