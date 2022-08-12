function for_with_break()
    arr = []
    for i = 0:3
        if i == 2
            break
        end
        push!(arr, i)
    end
    @assert(arr == [0, 1])
end

function for_with_continue()
    arr = []
    for i = 0:3
        if i == 2
            continue
        end
        push!(arr, i)
    end
    @assert(arr == [0, 1, 3])
end

function for_with_else()
    arr = []
    has_break = false
    for i = 0:3
        push!(arr, i)
    end
    if has_break != true
        push!(arr, 4)
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
    for i = 1:9
        push!(arr1, i)
    end
    arr2 = []
    num = 1:11
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
    seq = [1, 2, 3, 4, 5]
    seq_copy = collect(seq)
    for i = 0:length(seq)-2
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
        for j = 0:1
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
    x = x[end:-1:begin]
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
    append!(b, [3, 3])
    @assert(a == [1, 1, 3, 3])
    @assert(b == [1, 1, 3, 3])
end

function list_ops()
    a = Vector()
    push!(a, "test")
    @assert(a == ["test"])
    empty!(a)
    @assert(a == [])
    @assert(length(a) == 0)
    push!(a, "test1")
    push!(a, "test2")
    deleteat!(a, findfirst(isequal("test1"), a))
    @assert(a == ["test2"])
    @assert(length(a) == 1)
    empty!(a)
    push!(a, "test")
    b = copy(a)
    @assert(b == a)
    empty!(a)
    push!(a, "test2")
    push!(a, "test2")
    deleteat!(a, findfirst(isequal("test2"), a))
    @assert(count(isequal("test2"), a) == 1)
    empty!(a)
    push!(a, "test1")
    append!(a, b)
    @assert(a == ["test1", "test"])
    empty!(a)
    elems = ["1", "2", "3"]
    new_elems = []
    for e in elems
        push!(new_elems, repeat(e, 2))
    end
    @assert(new_elems == ["11", "22", "33"])
end

if abspath(PROGRAM_FILE) == @__FILE__
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
