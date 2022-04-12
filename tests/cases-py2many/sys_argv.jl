

function main()
    a::Vector{String} = sys.argv
    cmd::String = a[1]
    if cmd == "dart"
        #= pass =#
    else
        @assert(findfirst("sys_argv", cmd) != Nothing)
    end
    if length(a) > 1
        println(a[2])
    else
        println("OK")
    end
end

main()
