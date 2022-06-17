struct Foo

end

function bar(self::Foo)::String
    return "a"
end

if abspath(PROGRAM_FILE) == @__FILE__
    f = Foo()
    b = bar(f)
    println(join([b], " "))
end
