
function show()
    myfunc = (x, y) -> x + y
    println(join([myfunc(1, 2)], " "))
end

function main()
    show()
end

main()
