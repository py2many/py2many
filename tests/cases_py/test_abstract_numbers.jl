using Test
#= Unit tests for numbers.py. =#



abstract type AbstractTestNumbers end

mutable struct TestNumbers <: AbstractTestNumbers

end
function test_int(self::AbstractTestNumbers)
    @test Int64 <: Integer
    @test Int64 <: Complex
    @test (7 == Int64(7).real)
    @test (0 == Int64(7).imag)
    @test (7 == conjugate(Int64(7)))
    @test (-7 == conjugate(Int64(-7)))
    @test (7 == Int64(7).numerator)
    @test (1 == Int64(7).denominator)
end

function test_float(self::AbstractTestNumbers)
    @test !(Float64 <: Rational)
    @test Float64 <: Real
    @test (7.3 == Float64(7.3).real)
    @test (0 == Float64(7.3).imag)
    @test (7.3 == conjugate(Float64(7.3)))
    @test (-7.3 == conjugate(Float64(-7.3)))
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
    @test_throws TypeError Float64(c1)
    @test_throws TypeError Int64(c1)
end

function main()
    main()
end

main()
