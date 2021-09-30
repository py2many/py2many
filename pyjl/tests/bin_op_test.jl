
function mult_int_and_int()::Int64
a = 2
return a*2
end

function mult_float_and_int()::Float64
a = 2.0
return a*2
end

function mult_list_and_int()
a = []
for i in (0:10 - 1)
push!(a, i);
end
return repeat(a,2)
end

function add_two_lists()
a = []
b = []
for i in (0:10 - 1)
push!(a, i);
push!(b, i);
end
return [a;b]
end

function main()
println(mult_int_and_int());
println(mult_float_and_int());
println(mult_list_and_int());
println(add_two_lists());
end

main()
