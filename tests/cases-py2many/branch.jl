function something()::String
    return "test"
end

function lookup_and_write(values)
    output = nothing
    if length(values) == 1
        output = values[0]
    elseif length(values) == 2
        output = values[1]
    elseif length(values) == 3
        output = values[2]
    else
        output = values
    end
    return output
end

function lookup_and_write_without_else(values)
    output = nothing
    if length(values) == 1
        output = values[0]
    elseif length(values) == 2
        output = values[1]
    elseif length(values) == 3
        output = values[2]
    end
    return output
end

function main()
    @assert(lookup_and_write([]) == [])
    @assert(lookup_and_write([1]) == 1)
    @assert(lookup_and_write([1, 2]) == 2)
    @assert(lookup_and_write([1, 2, 3]) == 3)
    @assert(lookup_and_write([1, 2, 3, 4]) == [1, 2, 3, 4])
    @assert(lookup_and_write_without_else([]) === nothing)
    @assert(lookup_and_write_without_else([1]) == 1)
    @assert(lookup_and_write_without_else([1, 2]) == 2)
    @assert(lookup_and_write_without_else([1, 2, 3]) == 3)
    @assert(lookup_and_write_without_else([1, 2, 3, 4]) === nothing)
end

main()
