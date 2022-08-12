
function show()
    myfunc = (x, y) -> x + y
    return myfunc(1, 2)
end

if abspath(PROGRAM_FILE) == @__FILE__
    @assert(show() == 3)
end
