function show()
squares = Dict(x => x*x for x in 0:5 - 1)
println(join([length(squares)], " "));
evens = Dict(x => x*2 for x in 0:10 - 1 if x % 2 == 0 )
println(join([length(evens)], " "));
end

function main()
show();
end

main()
