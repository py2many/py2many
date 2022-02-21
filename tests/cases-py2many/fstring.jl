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
    a = 10
    @assert(join(["hello ", string(a + 1), " world"], "") == "hello 11 world")
    @assert(
        join(
            ["test ", string(a + 1), " test ", string(a + 20), " test ", string(a + 30)],
            "",
        ) == "test 11 test 30 test 40"
    )
    println("OK")
end

main()
