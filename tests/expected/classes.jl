abstract type AbstractFoo end
abstract type AbstractShape end
abstract type AbstractSquare end
abstract type AbstractPerson end
abstract type AbstractStudent end
abstract type AbstractWorker end
mutable struct Foo <: AbstractFoo
end
function bar(self::AbstractFoo)
    return baz(self)
end

function baz(self::AbstractFoo)::Int64
    return 10
end

function bar_str(self::AbstractFoo)::String
    return "a"
end

mutable struct Shape <: AbstractShape
    x
    y
end
function position(self::AbstractShape)
    return "($(self.x), $(self.y))"
end

mutable struct Square <: AbstractSquare
    #= Two-dimensional square =#
    x
    y
    side
    Square(x, y, side) = begin
        Shape(x, y)
        new(x, y, side)
    end
end
function area(self::AbstractSquare)
    self.x * self.y
end

mutable struct Person <: AbstractPerson
    name::String
end
function get_id(self::AbstractPerson)::String
    return self.name
end

mutable struct Student <: AbstractStudent
    name::String
    student_number::Int64
    domain::String
    Student(name::String, student_number::Int64, domain::String = "school.student.pt") =
        new(name, student_number, domain)
end
function get_id(self::AbstractStudent)
    return "$(self.name) - $(self.student_number)"
end

mutable struct Worker <: AbstractWorker
    name::String
    company_name::String
    hours_per_week::Int64
end

if abspath(PROGRAM_FILE) == @__FILE__
    f = Foo()
    b = bar(f)
    @assert(b == 10)
    c = bar_str(f)
    @assert(c == "a")
    shape = Shape(1, 3)
    square = Square(2, 4, 5)
    @assert(position(square) == "(2, 4)")
    p = Person("P")
    @assert(p.name == "P")
    @assert(get_id(p) == "P")
    s = Student("S", 111111)
    @assert(s.name == "S")
    @assert(s.student_number == 111111)
    @assert(s.domain == "school.student.pt")
    @assert(get_id(s) == "S - 111111")
    w = Worker("John", "Siemens", 35)
    @assert(w.name == "John")
    @assert(w.company_name == "Siemens")
    @assert(w.hours_per_week == 35)
    @assert(get_id(w) == "John")
    println("OK")
end
