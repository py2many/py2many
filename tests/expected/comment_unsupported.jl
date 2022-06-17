function do_unsupported()
    a = 1
    # dict comprehension ((key + 1), (value + 1)) unimplemented on line 9:4;
    b = Bool(a)
    println(join([b ? ("True") : ("False")], " "))
end

if abspath(PROGRAM_FILE) == @__FILE__
    do_unsupported()
end
