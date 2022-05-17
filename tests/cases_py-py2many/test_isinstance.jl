using Test




abstract type AbstractTestIsInstanceExceptions end
abstract type AbstractI end
abstract type AbstractC <: Abstractobject end
abstract type AbstractE <: Abstractobject end
abstract type AbstractD end
abstract type AbstractTestIsSubclassExceptions end
abstract type AbstractS <: AbstractC end
abstract type AbstractB end
abstract type AbstractAbstractClass <: Abstractobject end
abstract type AbstractAbstractInstance <: Abstractobject end
abstract type AbstractSuper end
abstract type AbstractChild <: AbstractSuper end
abstract type AbstractTestIsInstanceIsSubclass end
abstract type AbstractA end
abstract type AbstractX end
abstract type AbstractFailure <: Abstractobject end
mutable struct TestIsInstanceExceptions <: AbstractTestIsInstanceExceptions
__bases__
__class__

                    TestIsInstanceExceptions(__bases__ = property(getbases), __class__ = property(getclass)) =
                        new(__bases__, __class__)
end
function test_class_has_no_bases(self::C)
mutable struct I <: AbstractI
__class__

                    I(__class__ = property(getclass)) =
                        new(__class__)
end
function getclass(self::I)
return nothing
end

mutable struct C <: AbstractC
__bases__

                    C(__bases__ = property(getbases)) =
                        new(__bases__)
end
function getbases(self::C)::Tuple
return ()
end

assertEqual(self, false, isa(I(), C()))
end

function test_bases_raises_other_than_attribute_error(self::C)
mutable struct E <: AbstractE
__bases__

                    E(__bases__ = property(getbases)) =
                        new(__bases__)
end
function getbases(self::E)
throw(RuntimeError)
end

mutable struct I <: AbstractI
__class__

                    I(__class__ = property(getclass)) =
                        new(__class__)
end
function getclass(self::I)::E
return E()
end

mutable struct C <: AbstractC
__bases__

                    C(__bases__ = property(getbases)) =
                        new(__bases__)
end
function getbases(self::C)::Tuple
return ()
end

assertRaises(self, RuntimeError, isinstance, I(), C())
end

function test_dont_mask_non_attribute_error(self::C)
mutable struct I <: AbstractI

end

mutable struct C <: AbstractC
__bases__

                    C(__bases__ = property(getbases)) =
                        new(__bases__)
end
function getbases(self::C)
throw(RuntimeError)
end

assertRaises(self, RuntimeError, isinstance, I(), C())
end

function test_mask_attribute_error(self::C)
mutable struct I <: AbstractI

end

mutable struct C <: AbstractC
__bases__

                    C(__bases__ = property(getbases)) =
                        new(__bases__)
end
function getbases(self::C)
throw(AttributeError)
end

assertRaises(self, TypeError, isinstance, I(), C())
end

function test_isinstance_dont_mask_non_attribute_error(self::D)
mutable struct C <: AbstractC
__class__

                    C(__class__ = property(getclass)) =
                        new(__class__)
end
function getclass(self::C)
throw(RuntimeError)
end

c = C()
assertRaises(self, RuntimeError, isinstance, c, bool)
mutable struct D <: AbstractD

end

assertRaises(self, RuntimeError, isinstance, c, D)
end

mutable struct TestIsSubclassExceptions <: AbstractTestIsSubclassExceptions
__bases__

                    TestIsSubclassExceptions(__bases__ = property(getbases)) =
                        new(__bases__)
end
function test_dont_mask_non_attribute_error(self::S)
mutable struct C <: AbstractC
__bases__

                    C(__bases__ = property(getbases)) =
                        new(__bases__)
end
function getbases(self::C)
throw(RuntimeError)
end

mutable struct S <: AbstractS

end

assertRaises(self, RuntimeError, issubclass, C(), S())
end

function test_mask_attribute_error(self::S)
mutable struct C <: AbstractC
__bases__

                    C(__bases__ = property(getbases)) =
                        new(__bases__)
end
function getbases(self::C)
throw(AttributeError)
end

mutable struct S <: AbstractS

end

assertRaises(self, TypeError, issubclass, C(), S())
end

function test_dont_mask_non_attribute_error_in_cls_arg(self::C)
mutable struct B <: AbstractB

end

mutable struct C <: AbstractC
__bases__

                    C(__bases__ = property(getbases)) =
                        new(__bases__)
end
function getbases(self::C)
throw(RuntimeError)
end

assertRaises(self, RuntimeError, issubclass, B, C())
end

function test_mask_attribute_error_in_cls_arg(self::C)
mutable struct B <: AbstractB

end

mutable struct C <: AbstractC
__bases__

                    C(__bases__ = property(getbases)) =
                        new(__bases__)
end
function getbases(self::C)
throw(AttributeError)
end

assertRaises(self, TypeError, issubclass, B, C())
end

mutable struct AbstractClass <: AbstractAbstractClass
bases
__bases__

                    AbstractClass(bases, __bases__ = property(getbases)) =
                        new(bases, __bases__)
end
function getbases(self::AbstractClass)
return self.bases
end

function __call__(self::AbstractClass)::AbstractInstance
return AbstractInstance(self)
end

mutable struct AbstractInstance <: AbstractAbstractInstance
klass
__class__

                    AbstractInstance(klass, __class__ = property(getclass)) =
                        new(klass, __class__)
end
function getclass(self::AbstractInstance)
return self.klass
end

AbstractSuper = AbstractClass(())
AbstractChild = AbstractClass((AbstractSuper,))
mutable struct Super <: AbstractSuper

end

mutable struct Child <: AbstractChild

end

mutable struct TestIsInstanceIsSubclass <: AbstractTestIsInstanceIsSubclass
x::Int64
__bases__
end
function test_isinstance_normal(self::TestIsInstanceIsSubclass)
@test (true == isa(Super(), Super))
@test (false == isa(Super(), Child))
@test (false == isa(Super(), AbstractSuper))
@test (false == isa(Super(), AbstractChild))
@test (true == isa(Child(), Super))
@test (false == isa(Child(), AbstractSuper))
end

function test_isinstance_abstract(self::TestIsInstanceIsSubclass)
@test (true == isa(AbstractSuper(), AbstractSuper))
@test (false == isa(AbstractSuper(), AbstractChild))
@test (false == isa(AbstractSuper(), Super))
@test (false == isa(AbstractSuper(), Child))
@test (true == isa(AbstractChild(), AbstractChild))
@test (true == isa(AbstractChild(), AbstractSuper))
@test (false == isa(AbstractChild(), Super))
@test (false == isa(AbstractChild(), Child))
end

function test_isinstance_with_or_union(self::TestIsInstanceIsSubclass)
@test isa(Super(), __or__(Super, int))
@test !(isa(nothing, str | int))
@test isa(3, str | int)
@test isa("", str | int)
@test isa([], typing.List | typing.Tuple)
@test isa(2, typing.List | int)
@test !(isa(2, typing.List | typing.Tuple))
@test isa(nothing, int | nothing)
@test !(isa(3.14, int | str))
assertRaises(self, TypeError) do 
isa(2, list[int + 1])
end
assertRaises(self, TypeError) do 
isa(2, list[int + 1] | int)
end
assertRaises(self, TypeError) do 
isa(2, ((int | str) | list[int + 1]) | float)
end
end

function test_subclass_normal(self::TestIsInstanceIsSubclass)
@test (true == Super <: Super)
@test (false == Super <: AbstractSuper)
@test (false == Super <: Child)
@test (true == Child <: Child)
@test (true == Child <: Super)
@test (false == Child <: AbstractSuper)
@test Vector <: typing.List | typing.Tuple
@test !(Int64 <: typing.List | typing.Tuple)
end

function test_subclass_abstract(self::TestIsInstanceIsSubclass)
@test (true == AbstractSuper <: AbstractSuper)
@test (false == AbstractSuper <: AbstractChild)
@test (false == AbstractSuper <: Child)
@test (true == AbstractChild <: AbstractChild)
@test (true == AbstractChild <: AbstractSuper)
@test (false == AbstractChild <: Super)
@test (false == AbstractChild <: Child)
end

function test_subclass_tuple(self::TestIsInstanceIsSubclass)
@test (true == Child <: (Child,))
@test (true == Child <: (Super,))
@test (false == Super <: (Child,))
@test (true == Super <: (Child, Super))
@test (false == Child <: ())
@test (true == Super <: (Child, (Super,)))
@test (true == Int64 <: (int, (float, int)))
@test (true == String <: (str, (Child, str)))
end

function test_subclass_recursion_limit(self::TestIsInstanceIsSubclass)
infinite_recursion(support) do 
@test_throws RecursionError blowstack(issubclass, str, str)
end
end

function test_isinstance_recursion_limit(self::TestIsInstanceIsSubclass)
infinite_recursion(support) do 
@test_throws RecursionError blowstack(isinstance, "", str)
end
end

function test_subclass_with_union(self::TestIsInstanceIsSubclass)
@test Int64 <: (int | float) | int
@test String <: __or__(str, Child) | str
@test !(dict <: float | str)
@test !(object <: float | str)
assertRaises(self, TypeError) do 
2 <: __or__(Child, Super)
end
assertRaises(self, TypeError) do 
Int64 <: __or__(list[int + 1], Child)
end
end

function test_issubclass_refcount_handling(self::B)
mutable struct A <: AbstractA

end
function __bases__(self::A)::Tuple
return (int,)
end

mutable struct B <: AbstractB
x::Int64
end
function __bases__(self::B)::Tuple
return (A(),)
end

assertEqual(self, true, B() <: Int64)
end

function test_infinite_recursion_in_bases(self::X)
mutable struct X <: AbstractX
__bases__
end
function __bases__(self::X)
return self.__bases__
end

infinite_recursion(support) do 
assertRaises(self, RecursionError, issubclass, X(), int)
assertRaises(self, RecursionError, issubclass, int, X())
assertRaises(self, RecursionError, isinstance, 1, X())
end
end

function test_infinite_recursion_via_bases_tuple(self::Failure)
#= Regression test for bpo-30570. =#
mutable struct Failure <: AbstractFailure

end
function __getattr__(self::Failure, attr)::Tuple
return (self, nothing)
end

infinite_recursion(support) do 
assertRaises(self, RecursionError) do 
Failure() <: Int64
end
end
end

function test_infinite_cycle_in_bases(self::X)
#= Regression test for bpo-30570. =#
mutable struct X <: AbstractX

end
function __bases__(self::X)::Tuple
return (self, self, self)
end

infinite_recursion(support) do 
assertRaises(self, RecursionError, issubclass, X(), int)
end
end

function test_infinitely_many_bases(self::X)
#= Regression test for bpo-30570. =#
mutable struct X <: AbstractX

end
function __getattr__(self::B, attr)::Tuple
assertEqual(self, attr, "__bases__")
mutable struct A <: AbstractA

end

mutable struct B <: AbstractB

end

A.__getattr__ = X.__getattr__
B.__getattr__ = X.__getattr__
return (A(), B())
end

infinite_recursion(support) do 
assertRaises(self, RecursionError, issubclass, X(), int)
end
end

function blowstack(fxn, arg, compare_to)
tuple_arg = (compare_to,)
for cnt in 0:getrecursionlimit(sys) + 4
tuple_arg = (tuple_arg,)
fxn(arg, tuple_arg)
end
end

function main()
test_is_instance_exceptions = TestIsInstanceExceptions()
test_class_has_no_bases(test_is_instance_exceptions)
test_bases_raises_other_than_attribute_error(test_is_instance_exceptions)
test_dont_mask_non_attribute_error(test_is_instance_exceptions)
test_mask_attribute_error(test_is_instance_exceptions)
test_isinstance_dont_mask_non_attribute_error(test_is_instance_exceptions)
test_is_subclass_exceptions = TestIsSubclassExceptions()
test_dont_mask_non_attribute_error(test_is_subclass_exceptions)
test_mask_attribute_error(test_is_subclass_exceptions)
test_dont_mask_non_attribute_error_in_cls_arg(test_is_subclass_exceptions)
test_mask_attribute_error_in_cls_arg(test_is_subclass_exceptions)
test_is_instance_is_subclass = TestIsInstanceIsSubclass()
test_isinstance_normal(test_is_instance_is_subclass)
test_isinstance_abstract(test_is_instance_is_subclass)
test_isinstance_with_or_union(test_is_instance_is_subclass)
test_subclass_normal(test_is_instance_is_subclass)
test_subclass_abstract(test_is_instance_is_subclass)
test_subclass_tuple(test_is_instance_is_subclass)
test_subclass_recursion_limit(test_is_instance_is_subclass)
test_isinstance_recursion_limit(test_is_instance_is_subclass)
test_subclass_with_union(test_is_instance_is_subclass)
test_issubclass_refcount_handling(test_is_instance_is_subclass)
test_infinite_recursion_in_bases(test_is_instance_is_subclass)
test_infinite_recursion_via_bases_tuple(test_is_instance_is_subclass)
test_infinite_cycle_in_bases(test_is_instance_is_subclass)
test_infinitely_many_bases(test_is_instance_is_subclass)
end

main()