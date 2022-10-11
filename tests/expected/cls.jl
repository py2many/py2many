struct Foo

end

function bar(self)::String
    return "a"
end

function main()
    f = Foo()
    b = bar(f)
    println(b)
end

main()
