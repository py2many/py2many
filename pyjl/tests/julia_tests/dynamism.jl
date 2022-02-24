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

