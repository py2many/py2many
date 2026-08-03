function compare_with_integer_variable()
    i::Int64 = 0
    s::Int64 = 1
    if i != 0
        s = 2
    else

        s = 3
    end
    @assert(s == 3)
end

function use_zero_for_comparison()
    i::Int64 = 0
    s::Int64 = 1
    if false
        s = 2
    else

        s = 3
    end
    @assert(s == 3)
end

function main()
    compare_with_integer_variable()
    use_zero_for_comparison()
    println(join(["OK"], " "))
end

main()
