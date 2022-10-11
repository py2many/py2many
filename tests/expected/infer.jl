function foo()
    a = 10
    b = a
    @assert(b == 10)
    println(b)
end

function main()
    foo()
end

main()
