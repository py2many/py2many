function implicit_keys()::Bool
    CODES = Dict("KEY" => 1)
    return "KEY" ∈ keys(CODES)
end

function explicit_keys()::Bool
    CODES = Dict("KEY" => 1)
    return "KEY" ∈ keys(CODES)
end

function dict_values()::Bool
    CODES = Dict("KEY" => 1)
    return 1 ∈ values(CODES)
end

function return_dict_index_str(key::String)
    CODES = Dict("KEY" => 1)
    return CODES[key]
end

function return_dict_index_int(key::Int64)
    CODES = Dict(1 => "one")
    return CODES[key]
end

if abspath(PROGRAM_FILE) == @__FILE__
    @assert(implicit_keys())
    @assert(explicit_keys())
    @assert(dict_values())
    @assert(return_dict_index_str("KEY") == 1)
    @assert(return_dict_index_int(1) == "one")
    println("OK")
end
