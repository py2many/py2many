function for_with_break()
    arr = []
    for i in (0:3)
        if i == 2
            break
        end
        push!(arr, i)
    end
    @assert(arr == [0, 1])
end

function for_with_continue()
    arr = []
    for i in (0:3)
        if i == 2
            continue
        end
        push!(arr, i)
    end
    @assert(arr == [0, 1, 3])
end

function for_with_else()
    arr = []
    for i in (0:3)
        push!(arr, i)
    end
    @assert(arr == [0, 1, 2, 3, 4])
end

function while_with_break()
    arr = []
    i = 0
    while true
        if i == 2
            break
        end
        push!(arr, i)
        i += 1
    end
    @assert(arr == [0, 1])
end

function while_with_continue()
    arr = []
    i = 0
    while i < 5
        i += 1
        if i == 2
            continue
        end
        push!(arr, i)
    end
    @assert(arr == [1, 3, 4, 5])
end

function loop_range_test()
    arr1 = []
    for i in (1:9)
        push!(arr1, i)
    end
    arr2 = []
    num = (1:11)
    for i in num
        push!(arr2, i)
    end
    @assert(arr1 == [1, 2, 3, 4, 5, 6, 7, 8, 9])
    @assert(arr2 == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])
end

function loop_element_test()
    arr = [1, 2]
    res_1 = []
    for e in arr
        e[2]
        push!(res_1, e)
    end
    @assert(res_1 == [1, 2])
    arr_c = [2, 3, 4]
    res_2 = []
    for e in arr
        push!(res_2, arr_c[e+1])
    end
    @assert(res_2 == [3, 4])
end

function for_cycle_vars()
    seq::Vector{Int64} = [1, 2, 3, 4, 5]
    seq_copy::list = collect(seq)
    for i in (0:length(seq)-1-1)
        @assert(seq[i+1] == seq_copy[i+1])
    end
    complex_list = [([1, 2], 3, 4)]
    for ((a1, a2), b, c) in complex_list
        @assert(a1 == 1)
        @assert(a2 == 2)
        @assert(b == 3)
        @assert(c == 4)
        arr = []
        a = 1
        for j in (0:1)
            push!(arr, a)
            a += 1
        end
        @assert(arr[1] == 1)
        @assert(arr[2] == 2)
    end
    @assert(seq[1] == 1)
    @assert(seq[3] == 3)
    @assert(seq[end] == 5)
    x = 1
    @assert(seq[x+1] == 2)
end

function reversed_array()
    x = [1, 2, 3]
    x = x[begin:end]
    @assert(x == [3, 2, 1])
end

function list_of_lists()
    x = [[1, 2], [3, 4, 5, 6], [3, 4, 5, 6]]
    @assert(x[2][3] == 5)
    @assert(x[3][4] == 6)
end

function inplace_ops()
    a = [1, 1]
    b = a
    b = append!(b, [3, 3])
    @assert(a == [1, 1, 3, 3])
    @assert(b == [1, 1, 3, 3])
end

function list_ops()
    a = Vector()
    append(a, "test")
    @assert(a == ["test"])
    clear(a)
    @assert(a == [])
    @assert(length(a) == 0)
    append(a, "test1")
    append(a, "test2")
    remove(a, "test1")
    @assert(a == ["test2"])
    @assert(length(a) == 1)
    clear(a)
    append(a, "test")
    b = copy(a)
    @assert(b == a)
    clear(a)
    append(a, "test2")
    append(a, "test2")
    remove(a, "test2")
    @assert(count(a, "test2") == 1)
    clear(a)
    append(a, "test1")
    extend(a, b)
    @assert(a == ["test1", "test"])
    clear(a)
    elems = ["1", "2", "3"]
    new_elems = []
    for e in elems
        push!(new_elems, repeat(e, 2))
    end
    @assert(new_elems == ["11", "22", "33"])
end

function main()
    for_with_break()
    for_with_continue()
    while_with_break()
    while_with_continue()
    loop_range_test()
    for_cycle_vars()
    reversed_array()
    list_of_lists()
    inplace_ops()
    list_ops()
end

main()
