if abspath(PROGRAM_FILE) == @__FILE__
    a = [1, 2, 3]
    i = -1
    println(a[end])
    for i = -3:-1:-1
        println(a[i+1])
    end
end
