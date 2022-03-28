
function show()
    myfunc::Callable[[Int64, Int64], Int64] = (x, y) -> x + y
    println(myfunc(1, 2))
end

function main()
    show()
end

main()
