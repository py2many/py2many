foo(x) = x + 1

bar(x) = x - 1
bar(x::Int) = x + 1
bar(x::Real) = x * 2

baz(x::Real, y::Real) = x * y

barbaz(x, @nospecialize y) = x + y


# Show which function is invocated
@code_lowered foo(1)

@code_lowered bar(Int(1)) # Results in x + 1
@code_lowered bar(1.0) # Results in x - 1
@code_lowered bar(Int32(1)) # Results in x * 1

# Test code typed
@code_typed bar(Int(1))
@code_typed bar(1.0)
@code_typed bar(Int32(1))

@code_typed barbaz(1,2)
@code_typed barbaz(1,2.0)

# LLVM code
@code_llvm bar(Int(1))

@code_llvm barbaz(1, 2)
@code_llvm barbaz(1,2.0)


#################################
# Example of function with promote
function largest(a::Float64,b::Int64)
    if a > b
        c = a
    else
        c = b  
    end
    return c
end

function largest_with_promote(a::Float64,b::Int64)
    pa,pb = promote(a,b)
    if a > b
        c = pa
    else
        c = pb 
    end
    return c
end

@code_typed(largest(1.0, 2)) # Returns: Union{Int64, Float64}
@code_typed(largest_with_promote(1.0, 2)) # Returns: Float64

