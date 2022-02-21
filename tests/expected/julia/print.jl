function show()
    println(join(["b"], " "))
    println(join([2, "b"], " "))
    a::Float64 = 2.1
    println(join([a], " "))
    b = 2.1
    println(join([b], " "))
    c = true
    println(join([c ? ("True") : ("False")], " "))
end

function main()
    show()
end

main()
