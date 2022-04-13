
function make_tree(depth::Int64)::Tuple
    return depth == 0 ? ((nothing, nothing)) :
           ((make_tree(depth - 1), make_tree(depth - 1)))
end

function check_node(left, right)::Int64
    return left === nothing ? (1) : ((1 + check_node(left...)) + check_node(right...))
end

function run(depth::Int64)::Int64
    return check_node(make_tree(depth)...)
end

function main_func(requested_max_depth, min_depth = 4)
    io_lst::Vector = []
    max_depth = max(min_depth + 2, requested_max_depth)
    stretch_depth = max_depth + 1
    append(io_lst, "stretch tree of depth $(stretch_depth)\t check: $(run(stretch_depth))")
    long_lived_tree = make_tree(max_depth)
    mmd = max_depth + min_depth
    for test_depth in (min_depth:2:stretch_depth-1)
        tree_count = 2^(mmd - test_depth)
        check_sum = sum(map(run, repeat([(test_depth,)...], tree_count)))
        append(io_lst, "$(tree_count)\t trees of depth $(test_depth)\t check: $(check_sum)")
    end
    append(
        io_lst,
        "long lived tree of depth $(max_depth)\t check: $(check_node(long_lived_tree...))",
    )
    println(join(io_lst, "\n"))
end

function main()
    main_func(parse(Int, sys.argv[1]))
end

main()
