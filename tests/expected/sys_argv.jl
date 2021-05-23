

function main()
    a::Array{String} = append!([PROGRAM_FILE], ARGS)
    cmd::String = a[0+1]
    @assert(cmd != "")
    if length(a) > 1
        println(join([a[1+1]], " "))
    else

        println(join(["OK"], " "))
    end
end

main()
