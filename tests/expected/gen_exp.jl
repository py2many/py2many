function show()
gen = (x*x for x in 0:5 - 1)
for val in gen
println(join([val], " "));
end
end

function main()
show();
end

main()
