function show()
    println("b")
    println(2, "b")
    a::Float64 = 2.1
    println(a)
    b = 2.1
    println(b)
    c = true
    println(c ? ("True") : ("False"))
end

function main()
    show()
end

main()
