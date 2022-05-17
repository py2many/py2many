using Test

abstract type AbstractTypeAnnotationTests end
abstract type AbstractC end
abstract type AbstractD end
mutable struct TypeAnnotationTests <: AbstractTypeAnnotationTests
my_annotations::Dict
a::Int64
b::String
bases
d
name

                    TypeAnnotationTests(my_annotations::Dict, a::Int64 = 3, b::String = 4, bases = nothing, d = nothing, name = nothing) =
                        new(my_annotations, a, b, bases, d, name)
end
function test_lazy_create_annotations(self::TypeAnnotationTests)
foo = type_("Foo", (), Dict())
for i in 0:2
@test !("__annotations__" ∈ foo.__dict__)
d = foo.__annotations__
@test "__annotations__" ∈ foo.__dict__
@test (foo.__annotations__ == d)
@test (foo.__dict__["__annotations__"] == d)
#Delete Unsupported
del(foo.__annotations__)
end
end

function test_setting_annotations(self::TypeAnnotationTests)
foo = type_("Foo", (), Dict())
for i in 0:2
@test !("__annotations__" ∈ foo.__dict__)
d = Dict("a" => int)
foo.__annotations__ = d
@test "__annotations__" ∈ foo.__dict__
@test (foo.__annotations__ == d)
@test (foo.__dict__["__annotations__"] == d)
#Delete Unsupported
del(foo.__annotations__)
end
end

function test_annotations_getset_raises(self::TypeAnnotationTests)
assertRaises(self, AttributeError) do 
println(float.__annotations__)
end
assertRaises(self, TypeError) do 
float.__annotations__ = Dict()
end
assertRaises(self, TypeError) do 
#Delete Unsupported
del(float.__annotations__)
end
foo = type_("Foo", (), Dict())
foo.__annotations__ = Dict()
#Delete Unsupported
del(foo.__annotations__)
assertRaises(self, AttributeError) do 
#Delete Unsupported
del(foo.__annotations__)
end
end

function test_annotations_are_created_correctly(self::C)
mutable struct C <: AbstractC
a::Int64
b::String

                    C(a::Int64 = 3, b::String = 4) =
                        new(a, b)
end

assertTrue(self, "__annotations__" ∈ C.__dict__)
#Delete Unsupported
del(C.__annotations__)
assertFalse(self, "__annotations__" ∈ C.__dict__)
end

function test_descriptor_still_works(self::D)
mutable struct C <: AbstractC
my_annotations::Dict
bases
d
name

                    C(my_annotations::Dict, bases = nothing, d = nothing, name = nothing) =
                        new(my_annotations, bases, d, name)
end
function __annotations__(self::C)
if !hasattr(self, "my_annotations")
self.my_annotations = Dict()
end
if !isa(self.my_annotations, dict)
self.my_annotations = Dict()
end
return self.my_annotations
end

function __annotations__(self::C, value)
if !isa(value, dict)
throw(ValueError("can only set __annotations__ to a dict"))
end
self.my_annotations = value
end

function __annotations__(self::C)
if hasfield(self, "my_annotations"): getfield(self, "my_annotations" ? false === nothing
throw(AttributeError("__annotations__"))
end
self.my_annotations = nothing
end

c = C()
assertEqual(self, c.__annotations__, Dict())
d = Dict("a" => "int")
c.__annotations__ = d
assertEqual(self, c.__annotations__, d)
assertRaises(self, ValueError) do 
c.__annotations__ = 123
end
#Delete Unsupported
del(c.__annotations__)
assertRaises(self, AttributeError) do 
#Delete Unsupported
del(c.__annotations__)
end
assertEqual(self, c.__annotations__, Dict())
mutable struct D <: AbstractD

end

assertEqual(self, D.__annotations__, Dict())
d = Dict("a" => "int")
D.__annotations__ = d
assertEqual(self, D.__annotations__, d)
assertRaises(self, ValueError) do 
D.__annotations__ = 123
end
#Delete Unsupported
del(D.__annotations__)
assertRaises(self, AttributeError) do 
#Delete Unsupported
del(D.__annotations__)
end
assertEqual(self, D.__annotations__, Dict())
end
