function show()
    println(join(["b"], " "))
    println(join([2, "b"], " "))
    a::Float64 = 2.1
    println(join([a], " "))
    b = 2.1
    println(join([b], " "))
end

function main()
    show()
end
