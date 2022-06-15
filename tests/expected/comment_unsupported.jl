function do_unsupported()
    a = 1
    Dict(key + 1 => value + 1 for (key, value) in Dict())
    b = Bool(a)
    println(b ? ("True") : ("False"))
end

if abspath(PROGRAM_FILE) == @__FILE__
    do_unsupported()
end
