function main()
    a = [1, 2, 3]
    i = -1
    println(a[end])
    for i in (-1:-1:-5)
        println(a[i+1])
    end
end

main()
