
using Distributed

# Has to be at the top
addprocs(4)

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
# @everywhere begin

# end

function main_func(requested_max_depth, min_depth = 4)
    max_depth = max(min_depth + 2, requested_max_depth)
    stretch_depth = max_depth + 1
    println("stretch tree of depth $(stretch_depth)\t check: $(run(stretch_depth))")
    long_lived_tree = make_tree(max_depth)
    mmd = max_depth + min_depth
    if length(Sys.cpu_info()) > 1
        for test_depth in (min_depth:2:stretch_depth-1)
            tree_count = 2^(mmd - test_depth)
            check_sum = sum(
                pmap(
                    run,
                    repeat([(test_depth,)...], tree_count),
                    batch_size = (tree_count ÷ length(Sys.cpu_info())) + 1,
                    distributed = true,
                ),
            )
            println("$(tree_count)\t trees of depth $(test_depth)\t check: $(check_sum)")
        end
    else
        for test_depth in (min_depth:2:stretch_depth-1)
            tree_count = 2^(mmd - test_depth)
            check_sum = sum(map(run, repeat([(test_depth,)...], tree_count)))
            println("$(tree_count)\t trees of depth $(test_depth)\t check: $(check_sum)")
        end
    end
    println(
        "long lived tree of depth $(max_depth)\t check: $(check_node(long_lived_tree...))",
    )
end

function main()
    # main_func(parse(Int, append!([PROGRAM_FILE], ARGS)[2]))
    @time main_func(20)
end

main()
