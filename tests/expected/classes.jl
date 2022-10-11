struct Foo

end

function bar(self)::Int
    return baz(self)
end

function baz(self)::Int
    return 10
end

function main()
    f = Foo()
    b = bar(f)
    println(b)
    @assert(b == 10)
end

main()
