struct Foo
end
function bar(self::Foo)::Int64
return baz(self)
end

function baz(self::Foo)::Int64
return 10
end

struct Person
name::String
end
function __init__(self::Person, name::String)
self.name = name
end

function get_name(self::Person)
return self.name
end

struct Student
student_number::Int64
end
function __init__(self::Student, name::String, student_number::Int64)
__init__(super(), name);
self.student_number = student_number
end

function get_name(self::Student)
return join([string(self.student_number), " - ", string(self.name)], "")
end

function main()
f = Foo()
b = bar(f)
@assert(b == 10)
p = Person("Michael Carmichael")
s = Student("Michael Carmichael", 111111)
@assert(get_name(p) == "Michael Carmichael")
@assert(get_name(s) == "111111 - Michael Carmichael")
println("OK");
end

main()
