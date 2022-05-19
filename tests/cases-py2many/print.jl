
function show()
    println("b")
    println("$(2)b")
    a::Float64 = 2.1
    println(a)
    b = 2.1
    println(b)
    c = true
    println(c ? ("True") : ("False"))
    name = "test"
    val = true
    write(sys.stdout, "$(name)_vtables_dispatch_ = $(val)")
end

if abspath(PROGRAM_FILE) == @__FILE__
    show()
end
