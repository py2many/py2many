function nested_containers()::Bool
    CODES = Dict("KEY" => [1, 3])
    return 1 ∈ CODES["KEY"]
end

function main()
    if nested_containers()
        println("OK")
    end
end

main()
