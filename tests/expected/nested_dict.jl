function nested_containers()::Bool
    CODES = Dict("KEY" => [1, 3])
    return 1 in CODES["KEY"]
end

function main()
    if nested_containers()
        println(join(["OK"], " "))
    end
end

main()
