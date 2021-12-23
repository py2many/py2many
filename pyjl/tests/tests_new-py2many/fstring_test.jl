function main()
a = 10
b = "test"
c = 2 + 4
str1 = join(["hello ", string(a + 1), " world"], "")
@assert(str1 == "hello 11 world")
str2 = join(["hello ", string(b), " world ", string(a)], "")
@assert(str2 == "hello test world 10")
str3 = join(["hello ", string(b), " world ", string(a), " test ", string(c)], "")
@assert(str3 == "hello test world 10 test 6")
println("OK");
end

main()
