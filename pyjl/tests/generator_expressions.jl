function main()
value = join((string((x + y)) for x in (0:10 - 1), y in (0:8 - 1) if x > 4), " ")
println(value);
end

main()
