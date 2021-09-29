
function show_res()
a::Array{Int64} = []
for i in (0:10 - 1)
push!(a, i);
end
return repeat(a,2)
end

function show_res_add_two_lists()
a::Array{Int64} = []
b::Array{Int64} = []
for i in (0:10 - 1)
push!(a, i);
push!(b, i);
end
return [a;b]
end

function main()
println(join([show_res()], " "));
println(join([show_res_add_two_lists()], " "));
end

main()
