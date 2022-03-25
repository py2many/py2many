using Test
#= Unit tests for numbers.py. =#



abstract type AbstractTestNumbers end

mutable struct TestNumbers <: AbstractTestNumbers

end
function test_int(self::AbstractTestNumbers)
    @test int <: Integral
    @test int <: Complex
    @test (7 == parse(Int64, 7).real)
    @test (0 == parse(Int64, 7).imag)
    @test (7 == conjugate(parse(Int64, 7)))
    @test (-7 == conjugate(parse(Int64, -7)))
    @test (7 == parse(Int64, 7).numerator)
    @test (1 == parse(Int64, 7).denominator)
end

function test_float(self::AbstractTestNumbers)
    @test !(float <: Rational)
    @test float <: Real
    @test (7.3 == float(7.3).real)
    @test (0 == float(7.3).imag)
    @test (7.3 == conjugate(float(7.3)))
    @test (-7.3 == conjugate(float(-7.3)))
end

function test_complex(self::AbstractTestNumbers)
    @test !(complex <: Real)
    @test complex <: Complex
    c1, c2 = (complex(3, 2), complex(4, 1))
    @test_throws TypeError math.trunc(c1)
    # Lowered
    @test_throws TypeError operator.mod(c1)
    @test_throws TypeError operator.mod(c2)
    # Lowered
    @test_throws TypeError divmod(c1)
    @test_throws TypeError divmod(c2)
    # Lowered
    @test_throws TypeError operator.floordiv(c1)
    @test_throws TypeError operator.floordiv(c2)
    @test_throws TypeError float(c1)
    @test_throws TypeError int(c1)
end

function main()
    main()
end

main()
