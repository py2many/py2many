function multiply_list(elems)::Vector
new_elems = []
for e in elems
push!(new_elems, e*2);
end
return new_elems
end

function main()
a = Vector()
push!(a, "test");
@assert(a == ["test"])
empty!(a);
@assert(a == [])
@assert(length(a) == 0)
push!(a, "test1");
push!(a, "test2");
a = deleteat!(a, findfirst(isequal("test1"), a));
@assert(a == ["test2"])
@assert(length(a) == 1)
empty!(a);
push!(a, "test");
b = copy(a)
@assert(b == a)
empty!(a);
push!(a, "test2");
push!(a, "test2");
a = deleteat!(a, findfirst(isequal("test2"), a));
@assert(count(isequal("test2"), a) == 1)
empty!(a);
push!(a, "test1");
a = append!(a, b);
@assert(a == ["test1", "test"])
empty!(a);
elems = ["1", "2", "3"]
new_elems = multiply_list(elems)
@assert(new_elems == ["11", "22", "33"])
println("OK");
end

main()
