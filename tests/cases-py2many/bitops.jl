
function main()
    ands::Vector{Bool} = []
    ors::Vector{Bool} = []
    xors::Vector{Bool} = []
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
    println("OK")
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
