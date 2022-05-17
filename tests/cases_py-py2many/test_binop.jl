#= Tests for binary operators on subtypes of built-in types. =#
using Test


using abc: ABCMeta
abstract type AbstractRat <: Abstractobject end
abstract type AbstractRatTestCase end
abstract type AbstractOperationLogger end
abstract type AbstractA <: AbstractOperationLogger end
abstract type AbstractB <: AbstractOperationLogger end
abstract type AbstractC <: AbstractB end
abstract type AbstractV <: AbstractOperationLogger end
abstract type AbstractOperationOrderTests end
abstract type AbstractSupEq <: Abstractobject end
abstract type AbstractS <: AbstractSupEq end
abstract type AbstractF <: Abstractobject end
abstract type AbstractX <: Abstractobject end
abstract type AbstractSN <: AbstractSupEq end
abstract type AbstractXN end
abstract type AbstractFallbackBlockingTests end
function gcd(a, b)
#= Greatest common divisor using Euclid's algorithm. =#
while a
a, b = (b % a, a)
end
return b
end

function isint(x)
#= Test whether an object is an instance of int. =#
return isa(x, int)
end

function isnum(x)::Int64
#= Test whether an object is an instance of a built-in numeric type. =#
for T in (int, float, complex)
if isa(x, T)
return 1
end
end
return 0
end

function isRat(x)
#= Test whether an object is an instance of the Rat class. =#
return isa(x, Rat)
end

mutable struct Rat <: AbstractRat
#= Rational number implemented as a normalized pair of ints. =#
__den::Int64
__num::Int64
__radd__
__rmul__
__slots__::Vector{String}
den::Int64
num::Int64

            Rat(num = 0, den = 1, __radd__ = __add__, __rmul__ = __mul__, __slots__::Vector{String} = ["_Rat__num", "_Rat__den"]) = begin
                if !isint(num)
throw(TypeError("Rat numerator must be int (%r)" % num))
end
if !isint(den)
throw(TypeError("Rat denominator must be int (%r)" % den))
end
if den == 0
throw(ZeroDivisionError("zero denominator"))
end
                new(num , den , __radd__ , __rmul__ , __slots__)
            end
end
function _get_num(self::Rat)::Int64
#= Accessor function for read-only 'num' attribute of Rat. =#
return self.__num
end

function _get_den(self::Rat)::Int64
#= Accessor function for read-only 'den' attribute of Rat. =#
return self.__den
end

function __repr__(self::Rat)
#= Convert a Rat to a string resembling a Rat constructor call. =#
return "Rat(%d, %d)" % (self.__num, self.__den)
end

function __str__(self::Rat)::String
#= Convert a Rat to a string resembling a decimal numeric value. =#
return string(float(self))
end

function __float__(self::Rat)::Float64
#= Convert a Rat to a float. =#
return self.__num*1.0 / self.__den
end

function __int__(self::Rat)::Int64
#= Convert a Rat to an int; self.den must be 1. =#
if self.__den == 1
try
return Int(self.__num)
catch exn
if exn isa OverflowError
throw(OverflowError("%s too large to convert to int" % repr(self)))
end
end
end
throw(ValueError("can\'t convert %s to int" % repr(self)))
end

function __add__(self::Rat, other)::Union[Union[Union[Rat,float],Rat],float]
#= Add two Rats, or a Rat and a number. =#
if isint(other)
other = Rat(other)
end
if isRat(other)
return Rat(self.__num*other.__den + other.__num*self.__den, self.__den*other.__den)
end
if isnum(other) != 0
return float(self) + other
end
return NotImplemented
end

function __sub__(self::Rat, other)::Union[Union[Union[Rat,float],Rat],float]
#= Subtract two Rats, or a Rat and a number. =#
if isint(other)
other = Rat(other)
end
if isRat(other)
return Rat(self.__num*other.__den - other.__num*self.__den, self.__den*other.__den)
end
if isnum(other) != 0
return float(self) - other
end
return NotImplemented
end

function __rsub__(self::Rat, other)::Union[Union[Union[Rat,float],Rat],float]
#= Subtract two Rats, or a Rat and a number (reversed args). =#
if isint(other)
other = Rat(other)
end
if isRat(other)
return Rat(other.__num*self.__den - self.__num*other.__den, self.__den*other.__den)
end
if isnum(other) != 0
return other - float(self)
end
return NotImplemented
end

function __mul__(self::Rat, other)::Union[Union[Union[Union[Rat,float],Rat],Rat],float]
#= Multiply two Rats, or a Rat and a number. =#
if isRat(other)
return Rat(self.__num*other.__num, self.__den*other.__den)
end
if isint(other)
return Rat(self.__num*other, self.__den)
end
if isnum(other) != 0
return float(self)*other
end
return NotImplemented
end

function __truediv__(self::Rat, other)::Union[Union[Union[Union[Rat,float],Rat],Rat],float]
#= Divide two Rats, or a Rat and a number. =#
if isRat(other)
return Rat(self.__num*other.__den, self.__den*other.__num)
end
if isint(other)
return Rat(self.__num, self.__den*other)
end
if isnum(other) != 0
return float(self) / other
end
return NotImplemented
end

function __rtruediv__(self::Rat, other)::Union[Union[Union[Union[Rat,float],Rat],Rat],float]
#= Divide two Rats, or a Rat and a number (reversed args). =#
if isRat(other)
return Rat(other.__num*self.__den, other.__den*self.__num)
end
if isint(other)
return Rat(other*self.__den, self.__num)
end
if isnum(other) != 0
return other / float(self)
end
return NotImplemented
end

function __floordiv__(self::Rat, other)::Any
#= Divide two Rats, returning the floored result. =#
if isint(other)
other = Rat(other)
elseif !isRat(other)
return NotImplemented
end
x = self / other
return x.__num ÷ x.__den
end

function __rfloordiv__(self::Rat, other)::Any
#= Divide two Rats, returning the floored result (reversed args). =#
x = other / self
return x.__num ÷ x.__den
end

function __divmod__(self::Rat, other)::Tuple
#= Divide two Rats, returning quotient and remainder. =#
if isint(other)
other = Rat(other)
elseif !isRat(other)
return NotImplemented
end
x = self ÷ other
return (x, self - other*x)
end

function __rdivmod__(self::Rat, other)
#= Divide two Rats, returning quotient and remainder (reversed args). =#
if isint(other)
other = Rat(other)
elseif !isRat(other)
return NotImplemented
end
return div(other)
end

function __mod__(self::Rat, other)
#= Take one Rat modulo another. =#
return div(self)[2]
end

function __rmod__(self::Rat, other)
#= Take one Rat modulo another (reversed args). =#
return div(other)[2]
end

function __eq__(self::Rat, other)::Bool
#= Compare two Rats for equality. =#
if isint(other)
return self.__den == 1 && self.__num == other
end
if isRat(other)
return self.__num == other.__num && self.__den == other.__den
end
if isnum(other) != 0
return float(self) == other
end
return NotImplemented
end

mutable struct RatTestCase <: AbstractRatTestCase
#= Unit tests for Rat class and its support utilities. =#

end
function test_gcd(self::RatTestCase)
@test (gcd(10, 12) == 2)
@test (gcd(10, 15) == 5)
@test (gcd(10, 11) == 1)
@test (gcd(100, 15) == 5)
@test (gcd(-10, 2) == -2)
@test (gcd(10, -2) == 2)
@test (gcd(-10, -2) == -2)
for i in 1:19
for j in 1:19
@test gcd(i, j) > 0
@test gcd(-(i), j) < 0
@test gcd(i, -(j)) > 0
@test gcd(-(i), -(j)) < 0
end
end
end

function test_constructor(self::RatTestCase)
a = Rat(10, 15)
@test (a.num == 2)
@test (a.den == 3)
a = Rat(10, -15)
@test (a.num == -2)
@test (a.den == 3)
a = Rat(-10, 15)
@test (a.num == -2)
@test (a.den == 3)
a = Rat(-10, -15)
@test (a.num == 2)
@test (a.den == 3)
a = Rat(7)
@test (a.num == 7)
@test (a.den == 1)
try
a = Rat(1, 0)
catch exn
if exn isa ZeroDivisionError
#= pass =#
end
end
for bad in ("0", 0.0, 0im, (), [], Dict(), nothing, Rat, unittest)
try
a = Rat(bad)
catch exn
if exn isa TypeError
#= pass =#
end
end
try
a = Rat(1, bad)
catch exn
if exn isa TypeError
#= pass =#
end
end
end
end

function test_add(self::RatTestCase)
@test (Rat(2, 3) + Rat(1, 3) == 1)
@test (Rat(2, 3) + 1 == Rat(5, 3))
@test (1 + Rat(2, 3) == Rat(5, 3))
@test (1.0 + Rat(1, 2) == 1.5)
@test (Rat(1, 2) + 1.0 == 1.5)
end

function test_sub(self::RatTestCase)
@test (Rat(7, 2) - Rat(7, 5) == Rat(21, 10))
@test (Rat(7, 5) - 1 == Rat(2, 5))
@test (1 - Rat(3, 5) == Rat(2, 5))
@test (Rat(3, 2) - 1.0 == 0.5)
@test (1.0 - Rat(1, 2) == 0.5)
end

function test_mul(self::RatTestCase)
@test (Rat(2, 3)*Rat(5, 7) == Rat(10, 21))
@test (Rat(10, 3)*3 == 10)
@test (3*Rat(10, 3) == 10)
@test (Rat(10, 5)*0.5 == 1.0)
@test (0.5*Rat(10, 5) == 1.0)
end

function test_div(self::RatTestCase)
@test (Rat(10, 3) / Rat(5, 7) == Rat(14, 3))
@test (Rat(10, 3) / 3 == Rat(10, 9))
@test (2 / Rat(5) == Rat(2, 5))
@test (3.0*Rat(1, 2) == 1.5)
@test (Rat(1, 2)*3.0 == 1.5)
end

function test_floordiv(self::RatTestCase)
@test (Rat(10) ÷ Rat(4) == 2)
@test (Rat(10, 3) ÷ Rat(4, 3) == 2)
@test (Rat(10) ÷ 4 == 2)
@test (10 ÷ Rat(4) == 2)
end

function test_eq(self::RatTestCase)
@test (Rat(10) == Rat(20, 2))
@test (Rat(10) == 10)
@test (10 == Rat(10))
@test (Rat(10) == 10.0)
@test (10.0 == Rat(10))
end

function test_true_div(self::RatTestCase)
@test (Rat(10, 3) / Rat(5, 7) == Rat(14, 3))
@test (Rat(10, 3) / 3 == Rat(10, 9))
@test (2 / Rat(5) == Rat(2, 5))
@test (3.0*Rat(1, 2) == 1.5)
@test (Rat(1, 2)*3.0 == 1.5)
@test (eval("1/2") == 0.5)
end

mutable struct OperationLogger <: AbstractOperationLogger
#= Base class for classes with operation logging. =#
logger
end
function log_operation(self::OperationLogger)
logger(self, args...)
end

function op_sequence(op)::Vector
#= Return the sequence of operations that results from applying
    the operation `op` to instances of the given classes. =#
log = []
instances = []
for c in classes
push!(instances, c(log.append))
end
try
op(instances...)
catch exn
if exn isa TypeError
#= pass =#
end
end
return log
end

mutable struct A <: AbstractA

end
function __eq__(self::A, other)
log_operation(self, "A.__eq__")
return NotImplemented
end

function __le__(self::A, other)
log_operation(self, "A.__le__")
return NotImplemented
end

function __ge__(self::A, other)
log_operation(self, "A.__ge__")
return NotImplemented
end

mutable struct B <: AbstractB

end
function __eq__(self::B, other)
log_operation(self, "B.__eq__")
return NotImplemented
end

function __le__(self::B, other)
log_operation(self, "B.__le__")
return NotImplemented
end

function __ge__(self::B, other)
log_operation(self, "B.__ge__")
return NotImplemented
end

mutable struct C <: AbstractC

end
function __eq__(self::C, other)
log_operation(self, "C.__eq__")
return NotImplemented
end

function __le__(self::C, other)
log_operation(self, "C.__le__")
return NotImplemented
end

function __ge__(self::C, other)
log_operation(self, "C.__ge__")
return NotImplemented
end

mutable struct V <: AbstractV
#= Virtual subclass of B =#

end
function __eq__(self::V, other)
log_operation(self, "V.__eq__")
return NotImplemented
end

function __le__(self::V, other)
log_operation(self, "V.__le__")
return NotImplemented
end

function __ge__(self::V, other)
log_operation(self, "V.__ge__")
return NotImplemented
end

register(B, V)
mutable struct OperationOrderTests <: AbstractOperationOrderTests

end
function test_comparison_orders(self::OperationOrderTests)
@test (op_sequence(eq) == ["A.__eq__", "A.__eq__"])
@test (op_sequence(eq) == ["A.__eq__", "B.__eq__"])
@test (op_sequence(eq) == ["B.__eq__", "A.__eq__"])
@test (op_sequence(eq) == ["C.__eq__", "B.__eq__"])
@test (op_sequence(eq) == ["C.__eq__", "B.__eq__"])
@test (op_sequence(le) == ["A.__le__", "A.__ge__"])
@test (op_sequence(le) == ["A.__le__", "B.__ge__"])
@test (op_sequence(le) == ["B.__le__", "A.__ge__"])
@test (op_sequence(le) == ["C.__ge__", "B.__le__"])
@test (op_sequence(le) == ["C.__le__", "B.__ge__"])
@test V <: B
@test (op_sequence(eq) == ["B.__eq__", "V.__eq__"])
@test (op_sequence(le) == ["B.__le__", "V.__ge__"])
end

mutable struct SupEq <: AbstractSupEq
#= Class that can test equality =#

end
function __eq__(self::SupEq, other)::Bool
return true
end

mutable struct S <: AbstractS
#= Subclass of SupEq that should fail =#
__eq__

                    S(__eq__ = nothing) =
                        new(__eq__)
end

mutable struct F <: AbstractF
#= Independent class that should fall back =#

end

mutable struct X <: AbstractX
#= Independent class that should fail =#
__eq__

                    X(__eq__ = nothing) =
                        new(__eq__)
end

mutable struct SN <: AbstractSN
#= Subclass of SupEq that can test equality, but not non-equality =#
__ne__

                    SN(__ne__ = nothing) =
                        new(__ne__)
end

mutable struct XN <: AbstractXN
#= Independent class that can test equality, but not non-equality =#
__ne__

                    XN(__ne__ = nothing) =
                        new(__ne__)
end
function __eq__(self::XN, other)::Bool
return true
end

mutable struct FallbackBlockingTests <: AbstractFallbackBlockingTests
#= Unit tests for None method blocking =#

end
function test_fallback_rmethod_blocking(self::FallbackBlockingTests)
e, f, s, x = (SupEq(), F(), S(), X())
@test (e == e)
@test (e == f)
@test (f == e)
@test (e == x)
@test_throws TypeError eq(x, e)
@test_throws TypeError eq(e, s)
@test_throws TypeError eq(s, e)
end

function test_fallback_ne_blocking(self::FallbackBlockingTests)
e, sn, xn = (SupEq(), SN(), XN())
@test !(e != e)
@test_throws TypeError ne(e, sn)
@test_throws TypeError ne(sn, e)
@test !(e != xn)
@test_throws TypeError ne(xn, e)
end

function main()
rat_test_case = RatTestCase()
test_gcd(rat_test_case)
test_constructor(rat_test_case)
test_add(rat_test_case)
test_sub(rat_test_case)
test_mul(rat_test_case)
test_div(rat_test_case)
test_floordiv(rat_test_case)
test_eq(rat_test_case)
test_true_div(rat_test_case)
operation_order_tests = OperationOrderTests()
test_comparison_orders(operation_order_tests)
fallback_blocking_tests = FallbackBlockingTests()
test_fallback_rmethod_blocking(fallback_blocking_tests)
test_fallback_ne_blocking(fallback_blocking_tests)
end

main()