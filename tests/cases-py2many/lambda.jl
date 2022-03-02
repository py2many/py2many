
function show()
    myfunc::Callable[([int, int], int)] = (x, y) -> x + y
    println(myfunc(1, 2))
end

function main()
    show()
end

main()
