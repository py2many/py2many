
function demorgan(a::Bool, b::Bool)::Bool
a && b == !(!(a) || !(b));
end

@assert(!(demorgan))
check_sat();
