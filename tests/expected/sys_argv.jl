
if abspath(PROGRAM_FILE) == @__FILE__
    a = append!([PROGRAM_FILE], ARGS)
    cmd = a[1]
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
