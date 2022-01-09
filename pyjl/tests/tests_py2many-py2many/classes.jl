struct Foo end
function bar(self::Foo)::Int64
    return baz(self)
end

function baz(self::Foo)::Int64
    return 10
end

mutable struct Person
    name::string
end

function printname(self::Person)
    return self.name
end

mutable struct Student <: Person
    student_number::Int64
end

function printname(self::Student)
    return join([string(self.student_number), " - ", string(self.name)], "")
end

function main()
    f = Foo()
    b = bar(f)
    @assert(b == 10)
    p = Person("Michael Carmichael")
    s = Student("Michael Carmichael", 111111)
    @assert(printname(p) == "Michael Carmichael")
    @assert(printname(s) == "111111 - Michael Carmichael")
    println("OK")
end

main()
