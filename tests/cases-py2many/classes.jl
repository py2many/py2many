abstract type AbstractFoo end
abstract type AbstractPerson end
abstract type AbstractStudent <: AbstractPerson end
abstract type AbstractStudent2 <: AbstractPerson end
mutable struct Foo <: AbstractFoo

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

mutable struct Person <: AbstractPerson
    name::Any
end
function get_name(self::AbstractPerson)
    return self.name
end

mutable struct Student <: AbstractStudent
    student_number::Any
    name::Any
    domain::String

    Student(student_number::Any, name::Any, domain::String = "school.student.pt") =
        new(student_number, name, domain)
end
function get_name(self::AbstractStudent)
    return "$(self.student_number) - $(self.name)"
end

mutable struct Student2 <: AbstractStudent2
    student_number::Any
    name::Any
    domain::String

    Student2(name::String, student_number::Int64, domain::String = "school.student.pt") =
        begin
            if student_number < 0
                throw(ArgumentError("Student number must be a positive number"))
            end
            new(name, student_number, domain)
        end
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
    @assert(get_name(s) == "S - 111111")
    s2 = Student2("S2", 123)
    println("OK")
end

main()
