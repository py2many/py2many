function complex_test()
    c1 = 2 + 3im
    c2 = 4 + 5im
    c3 = c1 + c2
    @assert(c3 == 6 + 8im)
    c4 = c1 + 3
    @assert(c4 == 5 + 3im)
    c5 = c1 + 4im
    @assert(c5 == 2 + 7im)
    c6 = c3 - 2.3
    @assert(c6 == 3.7 + 8im)
end

function main()
    complex_test()
    println(join(["OK"], " "))
end

main()
