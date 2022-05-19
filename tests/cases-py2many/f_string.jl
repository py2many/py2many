if abspath(PROGRAM_FILE) == @__FILE__
    a = 10
    b = "test"
    c = 2 + 4
    str1 = "hello $(a + 1) world"
    @assert(str1 == "hello 11 world")
    str2 = "hello $(b) world $(a)"
    @assert(str2 == "hello test world 10")
    str3 = "hello $(b) world $(a) test $(c)"
    @assert(str3 == "hello test world 10 test 6")
    a = 10
    @assert("hello $(a + 1) world" == "hello 11 world")
    @assert("test $(a + 1) test $(a + 20) test $(a + 30)" == "test 11 test 30 test 40")
    a = 1
    str4 = "hello $(a + 1) world $(round(0.44444, digits=3))"
    @assert(str4 == "hello 2 world 0.444")
    println("OK")
end
