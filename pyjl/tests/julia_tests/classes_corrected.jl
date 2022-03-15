using Classes
using Parameters
abstract type AbstractPerson end
abstract type AbstractStudent <: AbstractPerson end

mutable struct Person <: AbstractPerson
    name::String
end
function __init__(self::AbstractPerson, name::String)
    self.name = name
end

function get_name(self::AbstractPerson)
    return self.name
end

mutable struct Student <: AbstractStudent
    name::String
    student_number::Int64
    domain::String

    Student(name, student_number, domain::String = "school.student.pt") = new(name, student_number, domain)
    Student(name, student_number, domain) = new(name, student_number, domain)
end

# @with_kw mutable struct Student <: AbstractStudent
#     name::String
#     student_number::Int64
#     domain::String = "school.student.pt"
# end

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
    @assert(s.domain == "school.student.pt")
    @assert(get_name(p) == "P")
    @assert(get_name(s) == "111111 - S")
    println("OK")
end

main()

# @macroexpand @with_kw mutable struct Student <: AbstractStudent
#     domain::String = "school.student.pt"
#     name::String
#     student_number::Int64
# end
