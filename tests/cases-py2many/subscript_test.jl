if abspath(PROGRAM_FILE) == @__FILE__
    l = [1, 2, 3]
    b = ["a", "b", "c"]
    x = 0
    @assert(l[x+2:end] == [2, 3])
    x = 1
    @assert(b[x+2:end] == ["c"])
    output = [1, 2, 3, 4, 5, 6]
    start = 1
    stop = 3
    @assert(output[begin:stop-start] == [1, 2])
    @assert(output[length(output):end] == [6])
    @assert(output[end] == 6)
    println("OK")
end
