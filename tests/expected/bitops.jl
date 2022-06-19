
function main_func()
    ands::Array{Bool} = []
    ors::Array{Bool} = []
    xors::Array{Bool} = []
    for a in [false, true]
        for b in [false, true]
            push!(ands, a & b)
            push!(ors, a | b)
            push!(xors, a ⊻ b)
        end
    end
    @assert(ands == [false, false, false, true])
    @assert(ors == [false, true, true, true])
    @assert(xors == [false, true, true, false])
    println(join(["OK"], " "))
end

function main()
    main_func()
end

main()
