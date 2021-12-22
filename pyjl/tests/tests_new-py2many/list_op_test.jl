function main()
a = Vector()
push!(a);
@assert(a == ["test"])
clear(a);
@assert(a == [])
@assert(length(a) == 0)
push!(a);
push!(a);
remove(a, "test1");
@assert(a == ["test2"])
@assert(length(a) == 1)
clear(a);
push!(a);
b = copy(a)
@assert(b == a)
clear(a);
push!(a);
push!(a);
remove(a, "test2");
@assert(count(a, "test2") == 1)
clear(a);
push!(a);
extend(a, b);
@assert(a == ["test1", "test"])
clear(a);
push!(a);
@assert(index(a, "test") == 0)
end

main()
