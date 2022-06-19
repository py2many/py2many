function do_unsupported()
    a = 1
    Dict(key + 1 => value + 1 for (key, value) in Dict())
    b = Bool(a)
    println(join([b ? ("True") : ("False")], " "))
end

function main()
    do_unsupported()
end

main()
