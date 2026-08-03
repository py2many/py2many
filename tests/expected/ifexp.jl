function show()
    a = 1
    b = a in [2, 3] ? (2) : (3)
    println(join([b], " "))
end

function main()
    show()
end

main()
