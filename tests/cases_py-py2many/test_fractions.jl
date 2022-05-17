#= Tests for Lib/fractions.py. =#
using Test
using decimal: Decimal




import fractions
import functools


using copy: copy, deepcopy

abstract type AbstractDummyFloat <: Abstractobject end
abstract type AbstractDummyRational <: Abstractobject end
abstract type AbstractDummyFraction <: Abstractfractions.Fraction end
abstract type AbstractFractionTest end
abstract type AbstractCustomValue end
abstract type Abstractmyint <: Abstractint end
F = fractions.Fraction
mutable struct DummyFloat <: AbstractDummyFloat
#= Dummy float class for testing comparisons with Fractions =#
value
__rsub__

            DummyFloat(value, __rsub__ = __sub__) = begin
                if !isa(value, float)
throw(TypeError("DummyFloat can only be initialized from float"))
end
                new(value, __rsub__ )
            end
end
function _richcmp(self::DummyFloat, other, op)
if isa(other, numbers.Rational)
return op(from_float(F, self.value), other)
elseif isa(other, DummyFloat)
return op(self.value, other.value)
else
return NotImplemented
end
end

function __eq__(self::DummyFloat, other)
return _richcmp(self, other, operator.eq)
end

function __le__(self::DummyFloat, other)
return _richcmp(self, other, operator.le)
end

function __lt__(self::DummyFloat, other)
return _richcmp(self, other, operator.lt)
end

function __ge__(self::DummyFloat, other)
return _richcmp(self, other, operator.ge)
end

function __gt__(self::DummyFloat, other)
return _richcmp(self, other, operator.gt)
end

function __float__(self::DummyFloat)
@assert(false)
end

function __sub__(self::DummyFloat, other)
@assert(false)
end

mutable struct DummyRational <: AbstractDummyRational
#= Test comparison of Fraction with a naive rational implementation. =#
num
den
end
function __eq__(self::DummyRational, other)
if isa(other, fractions.Fraction)
return self.num == other._numerator && self.den == other._denominator
else
return NotImplemented
end
end

function __lt__(self::DummyRational, other)::Bool
return (self.num*other._denominator) < (self.den*other._numerator)
end

function __gt__(self::DummyRational, other)::Bool
return (self.num*other._denominator) > (self.den*other._numerator)
end

function __le__(self::DummyRational, other)::Bool
return (self.num*other._denominator) <= (self.den*other._numerator)
end

function __ge__(self::DummyRational, other)::Bool
return (self.num*other._denominator) >= (self.den*other._numerator)
end

function __float__(self::DummyRational)
@assert(false)
end

mutable struct DummyFraction <: AbstractDummyFraction
#= Dummy Fraction subclass for copy and deepcopy testing. =#

end

function _components(r)::Tuple
return (r.numerator, r.denominator)
end

mutable struct FractionTest <: AbstractFractionTest
value
__lt__
denominator::Int64

                    FractionTest(value, __lt__ = __eq__, denominator::Int64 = 1) =
                        new(value, __lt__, denominator)
end
function assertTypedEquals(self::FractionTest, expected, actual)
#= Asserts that both the types and values are the same. =#
@test (type_(expected) == type_(actual))
@test (expected == actual)
end

function assertTypedTupleEquals(self::FractionTest, expected, actual)
#= Asserts that both the types and values in the tuples are the same. =#
assertTupleEqual(self, expected, actual)
assertListEqual(self, collect(map(type_, expected)), collect(map(type_, actual)))
end

function assertRaisesMessage(self::FractionTest, exc_type, message, callable)
#= Asserts that callable(*args, **kwargs) raises exc_type(message). =#
try
callable(args..., kwargs)
catch exn
 let e = exn
if e isa exc_type
@test (message == string(e))
end
end
end
end

function testInit(self::FractionTest)
@test ((0, 1) == _components(F()))
@test ((7, 1) == _components(F(7)))
@test ((7, 3) == _components(F(F(7, 3))))
@test ((-1, 1) == _components(F(-1, 1)))
@test ((-1, 1) == _components(F(1, -1)))
@test ((1, 1) == _components(F(-2, -2)))
@test ((1, 2) == _components(F(5, 10)))
@test ((7, 15) == _components(F(7, 15)))
@test ((10^23, 1) == _components(F(10^23)))
@test ((3, 77) == _components(F(F(3, 7), 11)))
@test ((-9, 5) == _components(F(2, F(-10, 9))))
@test ((2486, 2485) == _components(F(F(22, 7), F(355, 113))))
assertRaisesMessage(self, ZeroDivisionError, "Fraction(12, 0)", F)
@test_throws TypeError F(1.5 + 3im)
@test_throws TypeError F("3/2", 3)
@test_throws TypeError F(3, 0im)
@test_throws TypeError F(3, 1im)
@test_throws TypeError F(1, 2, 3)
end

function testInitFromFloat(self::FractionTest)
@test ((5, 2) == _components(F(2.5)))
@test ((0, 1) == _components(F(-0.0)))
@test ((3602879701896397, 36028797018963968) == _components(F(0.1)))
@test_throws ValueError F(float("nan"))
@test_throws OverflowError F(float("inf"))
@test_throws OverflowError F(float("-inf"))
end

function testInitFromDecimal(self::FractionTest)
@test ((11, 10) == _components(F(Decimal("1.1"))))
@test ((7, 200) == _components(F(Decimal("3.5e-2"))))
@test ((0, 1) == _components(F(Decimal(".000e20"))))
@test_throws ValueError F(Decimal("nan"))
@test_throws ValueError F(Decimal("snan"))
@test_throws OverflowError F(Decimal("inf"))
@test_throws OverflowError F(Decimal("-inf"))
end

function testFromString(self::FractionTest)
@test ((5, 1) == _components(F("5")))
@test ((3, 2) == _components(F("3/2")))
@test ((3, 2) == _components(F(" \n  +3/2")))
@test ((-3, 2) == _components(F("-3/2  ")))
@test ((13, 2) == _components(F("    013/02 \n  ")))
@test ((16, 5) == _components(F(" 3.2 ")))
@test ((-16, 5) == _components(F(" -3.2 ")))
@test ((-3, 1) == _components(F(" -3. ")))
@test ((3, 5) == _components(F(" .6 ")))
@test ((1, 3125) == _components(F("32.e-5")))
@test ((1000000, 1) == _components(F("1E+06")))
@test ((-12300, 1) == _components(F("-1.23e4")))
@test ((0, 1) == _components(F(" .0e+0\t")))
@test ((0, 1) == _components(F("-0.000e0")))
assertRaisesMessage(self, ZeroDivisionError, "Fraction(3, 0)", F)
assertRaisesMessage(self, ValueError, "Invalid literal for Fraction: \'3/\'", F)
assertRaisesMessage(self, ValueError, "Invalid literal for Fraction: \'/2\'", F)
assertRaisesMessage(self, ValueError, "Invalid literal for Fraction: \'3 /2\'", F)
assertRaisesMessage(self, ValueError, "Invalid literal for Fraction: \'3/+2\'", F)
assertRaisesMessage(self, ValueError, "Invalid literal for Fraction: \'+ 3/2\'", F)
assertRaisesMessage(self, ValueError, "Invalid literal for Fraction: \'3a2\'", F)
assertRaisesMessage(self, ValueError, "Invalid literal for Fraction: \'3/7.2\'", F)
assertRaisesMessage(self, ValueError, "Invalid literal for Fraction: \'3.2/7\'", F)
assertRaisesMessage(self, ValueError, "Invalid literal for Fraction: \'.\'", F)
end

function testImmutable(self::FractionTest)
r = F(7, 3)
__init__(r, 2, 15)
@test ((7, 3) == _components(r))
@test_throws AttributeError setattr(r, "numerator", 12)
@test_throws AttributeError setattr(r, "denominator", 6)
@test ((7, 3) == _components(r))
r._numerator = 4
r._denominator = 2
@test ((4, 2) == _components(r))
assertNotEqual(self, F(4, 2), r)
end

function testFromFloat(self::FractionTest)
@test_throws TypeError F.from_float(3 + 4im)
@test ((10, 1) == _components(from_float(F, 10)))
bigint = 1234567890123456789
@test ((bigint, 1) == _components(from_float(F, bigint)))
@test ((0, 1) == _components(from_float(F, -0.0)))
@test ((10, 1) == _components(from_float(F, 10.0)))
@test ((-5, 2) == _components(from_float(F, -2.5)))
@test ((99999999999999991611392, 1) == _components(from_float(F, 1e+23)))
@test (float(10^23) == float(from_float(F, 1e+23)))
@test ((3602879701896397, 1125899906842624) == _components(from_float(F, 3.2)))
@test (3.2 == float(from_float(F, 3.2)))
inf = inf
nan = inf - inf
assertRaisesMessage(self, OverflowError, "cannot convert Infinity to integer ratio", F.from_float)
assertRaisesMessage(self, OverflowError, "cannot convert Infinity to integer ratio", F.from_float)
assertRaisesMessage(self, ValueError, "cannot convert NaN to integer ratio", F.from_float)
end

function testFromDecimal(self::FractionTest)
@test_throws TypeError F.from_decimal(3 + 4im)
@test (F(10, 1) == from_decimal(F, 10))
@test (F(0) == from_decimal(F, Decimal("-0")))
@test (F(5, 10) == from_decimal(F, Decimal("0.5")))
@test (F(5, 1000) == from_decimal(F, Decimal("5e-3")))
@test (F(5000) == from_decimal(F, Decimal("5e3")))
@test (1 - F(1, 10^30) == from_decimal(F, Decimal("0." * repeat("9",30))))
assertRaisesMessage(self, OverflowError, "cannot convert Infinity to integer ratio", F.from_decimal)
assertRaisesMessage(self, OverflowError, "cannot convert Infinity to integer ratio", F.from_decimal)
assertRaisesMessage(self, ValueError, "cannot convert NaN to integer ratio", F.from_decimal)
assertRaisesMessage(self, ValueError, "cannot convert NaN to integer ratio", F.from_decimal)
end

function test_as_integer_ratio(self::FractionTest)
@test (as_integer_ratio(F(4, 6)) == (2, 3))
@test (as_integer_ratio(F(-4, 6)) == (-2, 3))
@test (as_integer_ratio(F(4, -6)) == (-2, 3))
@test (as_integer_ratio(F(0, 6)) == (0, 1))
end

function testLimitDenominator(self::FractionTest)
rpi = F("3.1415926535897932")
@test (limit_denominator(rpi, 10000) == F(355, 113))
@test (-limit_denominator(rpi, 10000) == F(-355, 113))
@test (limit_denominator(rpi, 113) == F(355, 113))
@test (limit_denominator(rpi, 112) == F(333, 106))
@test (limit_denominator(F(201, 200), 100) == F(1))
@test (limit_denominator(F(201, 200), 101) == F(102, 101))
@test (limit_denominator(F(0), 10000) == F(0))
for i in (0, -1)
assertRaisesMessage(self, ValueError, "max_denominator should be at least 1", F(1).limit_denominator)
end
end

function testConversions(self::FractionTest)
assertTypedEquals(self, -1, trunc(F(-11, 10)))
assertTypedEquals(self, 1, trunc(F(11, 10)))
assertTypedEquals(self, -2, floor(Int, F(-11, 10)))
assertTypedEquals(self, -1, ceil(math, F(-11, 10)))
assertTypedEquals(self, -1, ceil(math, F(-10, 10)))
assertTypedEquals(self, -1, parse(Int, F(-11, 10)))
assertTypedEquals(self, 0, round(F(-1, 10)))
assertTypedEquals(self, 0, round(F(-5, 10)))
assertTypedEquals(self, -2, round(F(-15, 10)))
assertTypedEquals(self, -1, round(F(-7, 10)))
@test (false == Bool(F(0, 1)))
@test (true == Bool(F(3, 2)))
assertTypedEquals(self, 0.1, float(F(1, 10)))
@test_throws OverflowError float(parse(Int, repeat("2",400) * "7"))
assertAlmostEqual(self, 2.0 / 3, float(F(parse(Int, repeat("2",400) * "7"), parse(Int, repeat("3",400) * "1"))))
assertTypedEquals(self, 0.1 + 0im, complex(F(1, 10)))
end

function testBoolGuarateesBoolReturn(self::CustomValue)
mutable struct CustomValue <: AbstractCustomValue
value
__lt__
denominator::Int64

                    CustomValue(value, __lt__ = __eq__, denominator::Int64 = 1) =
                        new(value, __lt__, denominator)
end
function __bool__(self::CustomValue)::Bool
return Bool(self.value)
end

function numerator(self::CustomValue)
return self
end

function __eq__(self::CustomValue, other)
throw(AssertionError("Avoid comparisons in Fraction.__bool__"))
end

register(numbers.Rational, CustomValue)
numerator = CustomValue(1)
r = F(numerator)
assertIs(self, r.numerator, numerator)
assertIs(self, Bool(r), true)
numerator = CustomValue(0)
r = F(numerator)
assertIs(self, Bool(r), false)
end

function testRound(self::FractionTest)
assertTypedEquals(self, F(-200), round(F(-150), digits = -2))
assertTypedEquals(self, F(-200), round(F(-250), digits = -2))
assertTypedEquals(self, F(30), round(F(26), digits = -1))
assertTypedEquals(self, F(-2, 10), round(F(-15, 100), digits = 1))
assertTypedEquals(self, F(-2, 10), round(F(-25, 100), digits = 1))
end

function testArithmetic(self::FractionTest)
@test (F(1, 2) == F(1, 10) + F(2, 5))
@test (F(-3, 10) == F(1, 10) - F(2, 5))
@test (F(1, 25) == F(1, 10)*F(2, 5))
@test (F(5, 6) == F(2, 3)*F(5, 4))
@test (F(1, 4) == F(1, 10) / F(2, 5))
@test (F(-15, 8) == F(3, 4) / F(-2, 5))
assertTypedEquals(self, 2, F(9, 10) ÷ F(2, 5))
assertTypedEquals(self, 10^23, F(10^23, 1) ÷ F(1))
@test (F(5, 6) == F(7, 3) % F(3, 2))
@test (F(2, 3) == F(-7, 3) % F(3, 2))
@test ((F(1), F(5, 6)) == div(F(7, 3)))
@test ((F(-2), F(2, 3)) == div(F(-7, 3)))
@test (F(8, 27) == F(2, 3)^F(3))
@test (F(27, 8) == F(2, 3)^F(-3))
assertTypedEquals(self, 2.0, F(4)^F(1, 2))
@test (F(1, 1) == +F(1, 1))
z = pow(F(-1), F(1, 2))
assertAlmostEqual(self, z.real, 0)
@test (z.imag == 1)
p = F(-1, 2)^0
@test (p == F(1, 1))
@test (p.numerator == 1)
@test (p.denominator == 1)
p = F(-1, 2)^-1
@test (p == F(-2, 1))
@test (p.numerator == -2)
@test (p.denominator == 1)
p = F(-1, 2)^-2
@test (p == F(4, 1))
@test (p.numerator == 4)
@test (p.denominator == 1)
end

function testLargeArithmetic(self::FractionTest)
assertTypedEquals(self, F(10101010100808080808080808101010101010000000000000000, 1010101010101010101010101011111111101010101010101010101010101), F(10^35 + 1, 10^27 + 1) % F(10^27 + 1, 10^35 - 1))
assertTypedEquals(self, F(7, 1901475900342344102245054808064), F(-(2^100), 3) % F(5, 2^100))
assertTypedTupleEquals(self, (9999999999999999, F(10101010100808080808080808101010101010000000000000000, 1010101010101010101010101011111111101010101010101010101010101)), div(F(10^35 + 1, 10^27 + 1)))
assertTypedEquals(self, -(2^200) ÷ 15, F(-(2^100), 3) ÷ F(5, 2^100))
assertTypedEquals(self, 1, F(5, 2^100) ÷ F(3, 2^100))
assertTypedEquals(self, (1, F(2, 2^100)), div(F(5, 2^100)))
assertTypedTupleEquals(self, (-(2^200) ÷ 15, F(7, 1901475900342344102245054808064)), div(F(-(2^100), 3)))
end

function testMixedArithmetic(self::FractionTest)
assertTypedEquals(self, F(11, 10), F(1, 10) + 1)
assertTypedEquals(self, 1.1, F(1, 10) + 1.0)
assertTypedEquals(self, 1.1 + 0im, F(1, 10) + (1.0 + 0im))
assertTypedEquals(self, F(11, 10), 1 + F(1, 10))
assertTypedEquals(self, 1.1, 1.0 + F(1, 10))
assertTypedEquals(self, 1.1 + 0im, (1.0 + 0im) + F(1, 10))
assertTypedEquals(self, F(-9, 10), F(1, 10) - 1)
assertTypedEquals(self, -0.9, F(1, 10) - 1.0)
assertTypedEquals(self, -0.9 + 0im, F(1, 10) - (1.0 + 0im))
assertTypedEquals(self, F(9, 10), 1 - F(1, 10))
assertTypedEquals(self, 0.9, 1.0 - F(1, 10))
assertTypedEquals(self, 0.9 + 0im, (1.0 + 0im) - F(1, 10))
assertTypedEquals(self, F(1, 10), F(1, 10)*1)
assertTypedEquals(self, 0.1, F(1, 10)*1.0)
assertTypedEquals(self, 0.1 + 0im, F(1, 10)*(1.0 + 0im))
assertTypedEquals(self, F(1, 10), 1*F(1, 10))
assertTypedEquals(self, 0.1, 1.0*F(1, 10))
assertTypedEquals(self, 0.1 + 0im, (1.0 + 0im)*F(1, 10))
assertTypedEquals(self, F(1, 10), F(1, 10) / 1)
assertTypedEquals(self, 0.1, F(1, 10) / 1.0)
assertTypedEquals(self, 0.1 + 0im, F(1, 10) / (1.0 + 0im))
assertTypedEquals(self, F(10, 1), 1 / F(1, 10))
assertTypedEquals(self, 10.0, 1.0 / F(1, 10))
assertTypedEquals(self, 10.0 + 0im, (1.0 + 0im) / F(1, 10))
assertTypedEquals(self, 0, F(1, 10) ÷ 1)
assertTypedEquals(self, 0.0, F(1, 10) ÷ 1.0)
assertTypedEquals(self, 10, 1 ÷ F(1, 10))
assertTypedEquals(self, 10^23, 10^22 ÷ F(1, 10))
assertTypedEquals(self, 1.0 ÷ 0.1, 1.0 ÷ F(1, 10))
assertTypedEquals(self, F(1, 10), F(1, 10) % 1)
assertTypedEquals(self, 0.1, F(1, 10) % 1.0)
assertTypedEquals(self, F(0, 1), 1 % F(1, 10))
assertTypedEquals(self, 1.0 % 0.1, 1.0 % F(1, 10))
assertTypedEquals(self, 0.1, F(1, 10) % float("inf"))
assertTypedEquals(self, float("-inf"), F(1, 10) % float("-inf"))
assertTypedEquals(self, float("inf"), F(-1, 10) % float("inf"))
assertTypedEquals(self, -0.1, F(-1, 10) % float("-inf"))
assertTypedTupleEquals(self, (0, F(1, 10)), div(F(1, 10)))
assertTypedTupleEquals(self, div(0.1), div(F(1, 10)))
assertTypedTupleEquals(self, (10, F(0)), div(1))
assertTypedTupleEquals(self, div(1.0), div(1.0))
assertTypedTupleEquals(self, div(0.1), div(F(1, 10)))
assertTypedTupleEquals(self, div(0.1), div(F(1, 10)))
assertTypedTupleEquals(self, div(-0.1), div(F(-1, 10)))
assertTypedTupleEquals(self, div(-0.1), div(F(-1, 10)))
assertTypedEquals(self, F(100, 1), F(1, 10)^-2)
assertTypedEquals(self, F(100, 1), F(10, 1)^2)
assertTypedEquals(self, 0.1, F(1, 10)^1.0)
assertTypedEquals(self, 0.1 + 0im, F(1, 10)^(1.0 + 0im))
assertTypedEquals(self, 4, 2^F(2, 1))
z = pow(-1, F(1, 2))
assertAlmostEqual(self, 0, z.real)
@test (1 == z.imag)
assertTypedEquals(self, F(1, 4), 2^F(-2, 1))
assertTypedEquals(self, 2.0, 4^F(1, 2))
assertTypedEquals(self, 0.25, 2.0^F(-2, 1))
assertTypedEquals(self, 1.0 + 0im, (1.0 + 0im)^F(1, 10))
@test_throws ZeroDivisionError operator.pow(F(0, 1), -2)
end

function testMixingWithDecimal(self::FractionTest)
@test_throws TypeError operator.add(F(3, 11), Decimal("3.1415926"))
@test_throws TypeError operator.add(Decimal("3.1415926"), F(3, 11))
end

function testComparisons(self::FractionTest)
@test F(1, 2) < F(2, 3)
@test !(F(1, 2) < F(1, 2))
@test F(1, 2) <= F(2, 3)
@test F(1, 2) <= F(1, 2)
@test !(F(2, 3) <= F(1, 2))
@test F(1, 2) == F(1, 2)
@test !(F(1, 2) == F(1, 3))
@test !(F(1, 2) != F(1, 2))
@test F(1, 2) != F(1, 3)
end

function testComparisonsDummyRational(self::FractionTest)
@test F(1, 2) == DummyRational(1, 2)
@test DummyRational(1, 2) == F(1, 2)
@test !(F(1, 2) == DummyRational(3, 4))
@test !(DummyRational(3, 4) == F(1, 2))
@test F(1, 2) < DummyRational(3, 4)
@test !(F(1, 2) < DummyRational(1, 2))
@test !(F(1, 2) < DummyRational(1, 7))
@test !(F(1, 2) > DummyRational(3, 4))
@test !(F(1, 2) > DummyRational(1, 2))
@test F(1, 2) > DummyRational(1, 7)
@test F(1, 2) <= DummyRational(3, 4)
@test F(1, 2) <= DummyRational(1, 2)
@test !(F(1, 2) <= DummyRational(1, 7))
@test !(F(1, 2) >= DummyRational(3, 4))
@test F(1, 2) >= DummyRational(1, 2)
@test F(1, 2) >= DummyRational(1, 7)
@test DummyRational(1, 2) < F(3, 4)
@test !(DummyRational(1, 2) < F(1, 2))
@test !(DummyRational(1, 2) < F(1, 7))
@test !(DummyRational(1, 2) > F(3, 4))
@test !(DummyRational(1, 2) > F(1, 2))
@test DummyRational(1, 2) > F(1, 7)
@test DummyRational(1, 2) <= F(3, 4)
@test DummyRational(1, 2) <= F(1, 2)
@test !(DummyRational(1, 2) <= F(1, 7))
@test !(DummyRational(1, 2) >= F(3, 4))
@test DummyRational(1, 2) >= F(1, 2)
@test DummyRational(1, 2) >= F(1, 7)
end

function testComparisonsDummyFloat(self::FractionTest)
x = DummyFloat(1.0 / 3.0)
y = F(1, 3)
@test x != y
@test x < y || x > y
@test !(x == y)
@test !(x <= y && x >= y)
@test y != x
@test y < x || y > x
@test !(y == x)
@test !(y <= x && y >= x)
end

function testMixedLess(self::FractionTest)
@test 2 < F(5, 2)
@test !(2 < F(4, 2))
@test F(5, 2) < 3
@test !(F(4, 2) < 2)
@test F(1, 2) < 0.6
@test !(F(1, 2) < 0.4)
@test 0.4 < F(1, 2)
@test !(0.5 < F(1, 2))
@test !(float("inf") < F(1, 2))
@test float("-inf") < F(0, 10)
@test !(float("nan") < F(-3, 7))
@test F(1, 2) < float("inf")
@test !(F(17, 12) < float("-inf"))
@test !(F(144, -89) < float("nan"))
end

function testMixedLessEqual(self::FractionTest)
@test 0.5 <= F(1, 2)
@test !(0.6 <= F(1, 2))
@test F(1, 2) <= 0.5
@test !(F(1, 2) <= 0.4)
@test 2 <= F(4, 2)
@test !(2 <= F(3, 2))
@test F(4, 2) <= 2
@test !(F(5, 2) <= 2)
@test !(float("inf") <= F(1, 2))
@test float("-inf") <= F(0, 10)
@test !(float("nan") <= F(-3, 7))
@test F(1, 2) <= float("inf")
@test !(F(17, 12) <= float("-inf"))
@test !(F(144, -89) <= float("nan"))
end

function testBigFloatComparisons(self::FractionTest)
@test !(F(10^23) == float(10^23))
@test !(1e+23 < float(F(trunc(1e+23) + 1)))
@test 1e+23 < F(trunc(1e+23) + 1)
@test !(1e+23 <= F(trunc(1e+23) - 1))
@test 1e+23 > F(trunc(1e+23) - 1)
@test !(1e+23 >= F(trunc(1e+23) + 1))
end

function testBigComplexComparisons(self::FractionTest)
@test !(F(10^23) == complex(10^23))
@test_throws TypeError operator.gt(F(10^23), complex(10^23))
@test_throws TypeError operator.le(F(10^23), complex(10^23))
x = F(3, 8)
z = complex(0.375, 0.0)
w = complex(0.375, 0.2)
@test x == z
@test !(x != z)
@test !(x == w)
@test x != w
for op in (operator.lt, operator.le, operator.gt, operator.ge)
@test_throws TypeError op(x, z)
@test_throws TypeError op(z, x)
@test_throws TypeError op(x, w)
@test_throws TypeError op(w, x)
end
end

function testMixedEqual(self::FractionTest)
@test 0.5 == F(1, 2)
@test !(0.6 == F(1, 2))
@test F(1, 2) == 0.5
@test !(F(1, 2) == 0.4)
@test 2 == F(4, 2)
@test !(2 == F(3, 2))
@test F(4, 2) == 2
@test !(F(5, 2) == 2)
@test !(F(5, 2) == float("nan"))
@test !(float("nan") == F(3, 7))
@test !(F(5, 2) == float("inf"))
@test !(float("-inf") == F(2, 5))
end

function testStringification(self::FractionTest)
@test ("Fraction(7, 3)" == repr(F(7, 3)))
@test ("Fraction(6283185307, 2000000000)" == repr(F("3.1415926535")))
@test ("Fraction(-1, 100000000000000000000)" == repr(F(1, -(10^20))))
@test ("7/3" == string(F(7, 3)))
@test ("7" == string(F(7, 1)))
end

function testHash(self::FractionTest)
hmod = sys.hash_info.modulus
hinf = sys.hash_info.inf
@test (hash(2.5) == hash(F(5, 2)))
@test (hash(10^50) == hash(F(10^50)))
assertNotEqual(self, hash(float(10^23)), hash(F(10^23)))
@test (hinf == hash(F(1, hmod)))
@test (hash(F(-1)) == __hash__(F(-1)))
end

function testApproximatePi(self::FractionTest)
three = F(3)
lasts, t, s, n, na, d, da = (0, three, 3, 1, 0, 0, 24)
while abs(s - lasts) > F(1, 10^9)
lasts = s
n, na = (n + na, na + 8)
d, da = (d + da, da + 32)
t = t*n / d
s += t
end
assertAlmostEqual(self, math.pi, s)
end

function testApproximateCos1(self::FractionTest)
x = F(1)
i, lasts, s, fact, num, sign = (0, 0, F(1), 1, 1, 1)
while abs(s - lasts) > F(1, 10^9)
lasts = s
i += 2
fact *= i*(i - 1)
num *= x*x
sign *= -1
s += (num / fact)*sign
end
assertAlmostEqual(self, cos(1), s)
end

function test_copy_deepcopy_pickle(self::FractionTest)
r = F(13, 7)
dr = DummyFraction(13, 7)
@test (r == loads(dumps(r)))
@test (id(r) == id(copy(r)))
@test (id(r) == id(deepcopy(r)))
assertNotEqual(self, id(dr), id(copy(dr)))
assertNotEqual(self, id(dr), id(deepcopy(dr)))
assertTypedEquals(self, dr, copy(dr))
assertTypedEquals(self, dr, deepcopy(dr))
end

function test_slots(self::FractionTest)
r = F(13, 7)
@test_throws AttributeError setattr(r, "a", 10)
end

function test_int_subclass(self::myint)
mutable struct myint <: Abstractmyint

end
function __mul__(self::myint, other)
return type_(self)(parse(Int, self)*parse(Int, other))
end

function __floordiv__(self::myint, other)
return type_(self)(parse(Int, self) ÷ parse(Int, other))
end

function __mod__(self::myint, other)
x = type_(self)(parse(Int, self) % parse(Int, other))
return x
end

function numerator(self::myint)
return type_(self)(parse(Int, self))
end

function denominator(self::myint)
return type_(self)(1)
end

f = Fraction(fractions, myint(1*3), myint(2*3))
assertEqual(self, f.numerator, 1)
assertEqual(self, f.denominator, 2)
assertEqual(self, type_(f.numerator), myint)
assertEqual(self, type_(f.denominator), myint)
end

function main()
fraction_test = FractionTest()
assertTypedEquals(fraction_test)
assertTypedTupleEquals(fraction_test)
assertRaisesMessage(fraction_test)
testInit(fraction_test)
testInitFromFloat(fraction_test)
testInitFromDecimal(fraction_test)
testFromString(fraction_test)
testImmutable(fraction_test)
testFromFloat(fraction_test)
testFromDecimal(fraction_test)
test_as_integer_ratio(fraction_test)
testLimitDenominator(fraction_test)
testConversions(fraction_test)
testBoolGuarateesBoolReturn(fraction_test)
testRound(fraction_test)
testArithmetic(fraction_test)
testLargeArithmetic(fraction_test)
testMixedArithmetic(fraction_test)
testMixingWithDecimal(fraction_test)
testComparisons(fraction_test)
testComparisonsDummyRational(fraction_test)
testComparisonsDummyFloat(fraction_test)
testMixedLess(fraction_test)
testMixedLessEqual(fraction_test)
testBigFloatComparisons(fraction_test)
testBigComplexComparisons(fraction_test)
testMixedEqual(fraction_test)
testStringification(fraction_test)
testHash(fraction_test)
testApproximatePi(fraction_test)
testApproximateCos1(fraction_test)
test_copy_deepcopy_pickle(fraction_test)
test_slots(fraction_test)
test_int_subclass(fraction_test)
end

main()