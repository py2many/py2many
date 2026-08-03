struct Foo

end

function bar(self::Foo)::String
    return "a"
end

function main()
    f = Foo()
    b = bar(f)
    println(join([b], " "))
end

main()
