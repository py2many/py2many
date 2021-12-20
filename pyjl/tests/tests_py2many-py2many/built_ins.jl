function default_builtins()
    a = str()
    b = bool()
    c = int()
    @assert(a == "")
    @assert(b == false)
    @assert(c == 0)
end

function main()
    a = max(1, 2)
    println(a)
    b = min(1, 2)
    println(b)
end

main()
