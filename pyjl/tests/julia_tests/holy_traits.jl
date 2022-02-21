# Tim Holy's idea of traits
# ALternative: https://github.com/mauro3/SimpleTraits.jl

abstract type AbstractPerson end
abstract type AbstractStudent <: AbstractPerson end
abstract type AbstractSomething end

# Normal Structs and functions
mutable struct Person <: AbstractPerson
    name::String
end

mutable struct Student <: AbstractStudent
    name::String
    student_number::Int
end

mutable struct Something <: AbstractPerson
    id::String
end

# Grouping methods
# TODO: Does not work with abstract types in traitfn
abstract type trait_student_something end
abstract type trait_person_something end
traitfn(::Student, ::Something) = trait_student_something
traitfn(::Person, ::Something) = trait_person_something

# Trait functions (Methods for dispatch)
get_name(x, y) = _get_name(x, y, traitfn(x, y))
_get_name(x, y, ::Type{trait_student_something}) =
    "$(x.student_number) - $(x.name) - $(y.id)"
_get_name(x, y, ::Type{trait_person_something}) =
    "$(x.name) - $(y.id)"

function main() 
    p = Person("Michael Carmichael")
    s = Student("Michael Other", 99999)
    sm = Something("wwww")
    @assert(get_name(s, sm) == "99999 - Michael Other - wwww")
    @assert(get_name(p, sm) == "Michael Carmichael - wwww")
end

main()