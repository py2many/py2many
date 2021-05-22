function implicit_keys()::Bool
    CODES = Dict("KEY" => 1)
    return "KEY" in keys(CODES)
end

function explicit_keys()::Bool
    CODES = Dict("KEY" => 1)
    return "KEY" in keys(CODES)
end

function dict_values()::Bool
    CODES = Dict("KEY" => 1)
    return 1 in values(CODES)
end

function main()
    @assert(implicit_keys())
    @assert(explicit_keys())
    @assert(dict_values())
    println(join(["OK"], " "))
end

main()
