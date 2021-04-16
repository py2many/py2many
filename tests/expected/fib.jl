function fib(i::Int64)::Int64
    if i == 0 || i == 1
        return 1
    end
    return (fib((i - 1)) + fib((i - 2)))
end

function main()
    rv = fib(5)
    println(join([rv], " "))
end
