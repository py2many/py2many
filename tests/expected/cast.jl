
function main_func()
    a = convert(Int16, 1)
    b = a
    println(join([b], " "))
    c = convert(Int64, 1)
    d = c
    println(join([d], " "))
    e = convert(UInt64, 1)
    f = e
    println(join([f], " "))
end

function main()
    main_func()
end

main()
