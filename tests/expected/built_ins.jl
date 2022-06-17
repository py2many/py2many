function default_builtins()
    a = ""
    b = false
    c = 0
    @assert(a == "")
    @assert(b == false)
    @assert(c == 0)
end

if abspath(PROGRAM_FILE) == @__FILE__
    a = max(1, 2)
    println(join([a], " "))
    b = min(1, 2)
    println(join([b], " "))
end
