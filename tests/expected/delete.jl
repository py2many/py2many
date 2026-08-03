function show()
    my_list = [1, 2, 3, 4, 5]
    # del unimplemented on line 7:4
    println(join([length(my_list)], " "))
    my_dict = Dict("a" => 1, "b" => 2, "c" => 3)
    # del unimplemented on line 12:4
    println(join([length(my_dict)], " "))
end

function main()
    show()
end

main()
