
function inline_pass()
#= pass 
=#
end

function inline_ellipsis()
#= ... 
=#
end

function indexing()::Int64
sum = 0
a::Vector = []
for i in (0:9)
push!(a, i);
sum += a[i + 1]
end
return sum
end

function infer_bool(code::Int64)::Bool
return code in [1, 2, 4]
end

function show()
a1 = 10
b1 = 15
b2 = 15
@assert(b1 == 15)
@assert(b2 == 15)
b9 = 2
b10 = 2
@assert(b9 == b10)
a2::Float64 = 2.1
println(a2);
for i in (0:9)
println(i);
end
for i in (0:2:9)
println(i);
end
a3 = -(a1)
a4 = (a3 + a1)
println(a4);
t1 = a1 > 5 ? (10) : (5)
@assert(t1 == 10)
sum1 = indexing()
println(sum1);
a5 = [1, 2, 3]
println(length(a5));
a9::Vector{String} = ["a", "b", "c", "d"]
println(length(a9));
a7 = Dict("a" => 1, "b" => 2)
println(length(a7));
a8 = true
if a8
println("true");
else

if a4 > 0
println("never get here");
end


end
if a1 == 11
println("false");
else

println("true");


end
if 1 != nothing
println("World is sane");
end
println(true ? ("True") : ("False"));
if true
a1 += 1
end
@assert(a1 == 11)
if true
println("true");
end
inline_pass();
s = "1    2"
println(s);
@assert(infer_bool(1))
_escape_quotes = " foo \"bar\" baz "
@assert(findfirst("bbc", "aaabbccc") != Nothing)
@assert(Bool(1))
2;
_c1, _c2 = (1, 3)
end

function main()
show();
end

main()