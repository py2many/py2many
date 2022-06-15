
function test_method(
    fdesc,
    entry,
    defaultNamedOptArg,
    defaultNamedNotOptArg,
    defaultUnnamedArg,
    is_comment = true,
)
    return "$(fdesc), $(entry), $(defaultNamedOptArg),$(defaultNamedNotOptArg),$(defaultUnnamedArg)"
end

function show()
    println("b")
    println("2 b")
    a::Float64 = 2.1
    println(a)
    b = 2.1
    println(b)
    c = true
    println(c ? ("True") : ("False"))
    name = "test"
    val = true
    write(stdout, "$(name)_vtables_dispatch_ = $(val)")
    name = "test_method"
    fdesc = "self"
    entry = "some_entry"
    write(
        stdout,
        "#\tdef $(name)(self$(test_method(fdesc, entry, "defaultNamedOptArg", "defaultNamedNotOptArg", "defaultUnnamedArg"))):",
    )
    indent = 2
    test = "test"
    println("$(repeat(" ",indent)) $(test)")
end

if abspath(PROGRAM_FILE) == @__FILE__
    show()
end
