function do_unsupported()
    a = 1
    # dict comprehension ((key + 1), (value + 1)) unimplemented on line 9:4;
    b = Bool(a)
    println(join([b ? ("True") : ("False")], " "))
end

function main()
    do_unsupported()
end

main()
