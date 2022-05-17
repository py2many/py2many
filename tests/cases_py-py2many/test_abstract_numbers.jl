#= Unit tests for numbers.py. =#
using Test




abstract type AbstractTestNumbers end
mutable struct TestNumbers <: AbstractTestNumbers

end
function test_int(self::TestNumbers)
@test Int64 <: Integer
@test (7 == Int(7).real)
@test (0 == Int(7).imag)
@test (7 == conj(Int(7)))
@test (-7 == conj(Int(-7)))
@test (7 == Int(7).numerator)
@test (1 == Int(7).denominator)
end

function test_float(self::TestNumbers)
@test !(Float64 <: Rational)
@test Float64 <: Real
@test (7.3 == float(7.3).real)
@test (0 == float(7.3).imag)
@test (7.3 == conj(float(7.3)))
@test (-7.3 == conj(float(-7.3)))
end

function test_complex(self::TestNumbers)
@test !(Complex <: Real)
@test Complex <: Complex
c1, c2 = (complex(3, 2), complex(4, 1))
@test_throws TypeError trunc(c1)
@test_throws TypeError mod(c1, c2)
@test_throws TypeError divmod(c1, c2)
@test_throws TypeError div(c1, c2)
@test_throws TypeError float(c1)
@test_throws TypeError int(c1)
end

function main()
test_numbers = TestNumbers()
test_int(test_numbers)
test_float(test_numbers)
test_complex(test_numbers)
end

main()