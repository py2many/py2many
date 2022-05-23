
function show()
    myfunc = (x, y) -> x + y
    println(myfunc(1, 2))
end

if abspath(PROGRAM_FILE) == @__FILE__
    show()
end
