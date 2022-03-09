abstract type AbstractFoo end
abstract type AbstractPerson end
abstract type AbstractStudent <: AbstractPerson end
struct Foo <: AbstractFoo

end
function bar(self::AbstractFoo)::Int64
    return baz(self)
end

function baz(self::AbstractFoo)::Int64
    return 10
end

function bar_str(self::AbstractFoo)::String
    return "a"
end

struct Person <: AbstractPerson
    name::String
end
function __init__(self::AbstractPerson, name::String)
    self.name = name
end

function get_name(self::AbstractPerson)
    return self.name
end

struct Student <: Person
    name::String
    student_number::Int64
end
function __init__(self::AbstractStudent, name::String, student_number::Int64)
    self.name = name
    self.student_number = student_number
end

function get_name(self::AbstractStudent)
    return "$(self.student_number) - $(self.name)"
end

function main()
    f = Foo()
    b = bar(f)
    @assert(b == 10)
    c = bar_str(f)
    @assert(c == "a")
    p = Person("P")
    s = Student("S", 111111)
    @assert(get_name(p) == "P")
    @assert(get_name(s) == "111111 - S")
    println("OK")
end

main()
