function foo()
    a = 10
    b = a
    @assert(b == 10)
    println(join([b], " "))
end

if abspath(PROGRAM_FILE) == @__FILE__
    foo()
end
