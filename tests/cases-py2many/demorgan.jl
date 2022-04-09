
function demorgan(a::Bool, b::Bool)::Bool
    return (a && b) == !(!(a) || !(b))
end

@assert(demorgan(true, true))
@assert(demorgan(true, false))
@assert(demorgan(false, true))
@assert(demorgan(false, false))
println("OK")
