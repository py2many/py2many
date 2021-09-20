
function show_res()
a::Array{Int64} = []
for i in (0:10 - 1)
push!(a, i);
end
return repeat(a,2)
end

function main()
println(join([show_res()], " "));
end

main()
