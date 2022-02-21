

function main()
    a::Array{String} = append!([PROGRAM_FILE], ARGS)
    cmd::String = a[0+1]
    if cmd == "dart"
        # pass
    else

        @assert(findfirst("sys_argv", cmd) != Nothing)
    end
    if length(a) > 1
        println(join([a[1+1]], " "))
    else

        println(join(["OK"], " "))
    end
end

main()
