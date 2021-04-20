function show()
    a1 = 10
    a2::Float64 = 2.1
    println(join([a2], " "))
    for i in (0:10-1)
        println(join([i], " "))
    end
    for i in (0:2:10-1)
        println(join([i], " "))
    end
    a3 = -(a1)
    a4 = (a3 + a1)
    println(join([a4], " "))
end

function main()
    show()
end

main()
