function show()
    my_list = [1, 2, 3, 4, 5]
    deleteat!(my_list, 2 + 1)
    println(join([length(my_list)], " "))
    my_dict = Dict("a" => 1, "b" => 2, "c" => 3)
    delete!(my_dict, "b")
    println(join([length(my_dict)], " "))
end

function main()
    show()
end

main()
