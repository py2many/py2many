function something()
println("Something");
end

function lookup_and_write(values, start, stop)
if isinstance(values, bytearray)
output = values
elseif 1 == 2
println("Never reach");
elseif 2 == 1
println("Never reach");
elseif 3 == 1
println("Never reach");
else
output = bytearray()
output[(begin + 1):stop - start] = something()
end

function main()
lookup_and_write([1, 2], 0, 1);
end

main()
