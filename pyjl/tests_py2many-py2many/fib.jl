function fib(i::Int64)::Int64
if i == 0 || i == 1
return 1
end
return (fib((i - 1)) + fib((i - 2)))
end

function main()
println(fib(5));
end

main()
