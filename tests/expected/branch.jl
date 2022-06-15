function something()::String
    return "test"
end

function lookup_and_write(values::list{Any})
    output = nothing
    if length(values) == 1
        output = values[1]
    elseif length(values) == 2
        output = values[2]
    elseif length(values) == 3
        output = values[3]
    else
        output = values
    end
    return output
end

function lookup_and_write_without_else(values::list{Any})
    output = nothing
    if length(values) == 1
        output = values[1]
    elseif length(values) == 2
        output = values[2]
    elseif length(values) == 3
        output = values[3]
    end
    return output
end

if abspath(PROGRAM_FILE) == @__FILE__
    @assert(lookup_and_write(convert(list{Any}, [])) == [])
    @assert(lookup_and_write(convert(list{Any}, [1])) == 1)
    @assert(lookup_and_write(convert(list{Any}, [1, 2])) == 2)
    @assert(lookup_and_write(convert(list{Any}, [1, 2, 3])) == 3)
    @assert(lookup_and_write(convert(list{Any}, [1, 2, 3, 4])) == [1, 2, 3, 4])
    @assert(lookup_and_write_without_else(convert(list{Any}, [])) === nothing)
    @assert(lookup_and_write_without_else(convert(list{Any}, [1])) == 1)
    @assert(lookup_and_write_without_else(convert(list{Any}, [1, 2])) == 2)
    @assert(lookup_and_write_without_else(convert(list{Any}, [1, 2, 3])) == 3)
    @assert(lookup_and_write_without_else(convert(list{Any}, [1, 2, 3, 4])) === nothing)
end
