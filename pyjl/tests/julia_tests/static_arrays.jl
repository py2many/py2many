# This code is courtesy of: https://blog.sintef.com/industry-en/writing-type-stable-julia-code/

using StaticArrays
SA = SVector{3,Float64}([1.,2.,3.])
SA = SVector(1.,2.,3.)

# The following code is not type-stable. It will show with @code_warntype
# The Length is part of an arrays value, not its type.
SA = SVector([1.,2.,3.]) 


# Creating a type-stable Julia function using Val
# Val allows to move type instability up the call hierarchy, or eliminate it altogether.
function static(v,::Val{L}) where{L}
    return SVector{L,Float64}(v)
end
function foo()
    Val3 = Val(3)
    Val4 = Val(4)
    @show static([1.,2.,3.]   ,Val3)
    @show static([1.,2.,3.,4.],Val4)
end

# Detects type instability
@code_warntype(foo())