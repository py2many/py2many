
function mult_int_and_int()::Int64
    a = 2
    return a * 2
end

function mult_float_and_int()::Float64
    a = 2.0
    return a * 2
end

function mult_string_and_int()::String
    a::String = "test"
    return repeat(a, 2)
end

function mult_int_and_string()::String
    a::Int64 = 2
    return repeat("test", a)
end

function mult_int_and_bool()::Int64
    a::Bool = false
    return a * 1
end

function mult_bool_and_string()::Int64
    a::Int64 = 1
    return a * false
end

function mult_list_and_int()::Vector
    a::Vector{Int64} = []
    for i = 0:9
        push!(a, i)
    end
    return repeat(a, 2)
end

function mult_tuple_and_int()
    mul_1 = repeat([(1,)...], 2)
    a = (1,)
    mul_2 = repeat([a...], 2)
    @assert(mul_1 == mul_2)
end

function add_two_lists()
    a::Vector{Int64} = []
    b::Vector{Int64} = []
    for i = 0:9
        push!(a, i)
        push!(b, i)
    end
    return append!(a, b)
end

function and_op_int_and_int()::Int64
    a::Int64 = 2
    return a & 2
end

function or_op_int_and_int()::Int64
    a::Int64 = 2
    return a | 1
end

function arithmetic_shift_right_int_and_int()::Int64
    a::Int64 = 2
    return a >> 1
end

function arithmetic_shift_left_int_and_int()::Int64
    a::Int64 = 2
    return a << 1
end

function nested_bin_op()::Int64
    a::Int64 = 10
    return a * (10 + 20) + a * (2 + (4 + 8 * (6 + 3)) * 80)
end

if abspath(PROGRAM_FILE) == @__FILE__
    @assert(mult_int_and_int() == 4)
    @assert(mult_float_and_int() == 4.0)
    @assert(mult_string_and_int() == "testtest")
    @assert(mult_int_and_string() == "testtest")
    @assert(
        mult_list_and_int() == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    )
    @assert(add_two_lists() == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9])
    @assert(mult_int_and_bool() == 0)
    @assert(mult_bool_and_string() == 0)
    @assert(and_op_int_and_int() == 2)
    @assert(or_op_int_and_int() == 3)
    @assert(arithmetic_shift_right_int_and_int() == 1)
    @assert(arithmetic_shift_left_int_and_int() == 4)
    @assert(nested_bin_op() == 61120)
    mult_tuple_and_int()
end
