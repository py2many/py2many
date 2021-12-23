function main()
a = 10
@assert(join(["hello ", string(a + 1), " world"], "") == "hello 11 world")
@assert(join(["test ", string(a + 1), " test ", string(a + 20), " test ", string(a + 30)], "") == "test 11 test 30 test 40")
println("OK");
end

main()
