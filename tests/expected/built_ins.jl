function default_builtins()
    a = string()
    b = false
    c = zero(Int)
    d = zero(Float64)
    @assert(a == "")
    @assert(b == false)
    @assert(c == 0)
    @assert(d == 0.0)
end

if abspath(PROGRAM_FILE) == @__FILE__
    default_builtins()
    a = max(1, 2)
    @assert(a == 2)
    b = min(1, 2)
    @assert(b == 1)
    println("OK")
end
