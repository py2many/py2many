#= Test compiler changes for unary ops (+, -, ~) introduced in Python 2.2 =#
using Test

abstract type AbstractUnaryOpTestCase end
mutable struct UnaryOpTestCase <: AbstractUnaryOpTestCase

end
function test_negative(self::UnaryOpTestCase)
@test -2 == (0 - 2)
@test (-0 == 0)
@test (-(-2) == 2)
@test -2 == (0 - 2)
@test -2.0 == (0 - 2.0)
@test -2im == (0 - 2im)
end

function test_positive(self::UnaryOpTestCase)
@test (+2 == 2)
@test (+0 == 0)
@test (+(+2) == 2)
@test (+2 == 2)
@test (+2.0 == 2.0)
@test (+2im == 2im)
end

function test_invert(self::UnaryOpTestCase)
@test -2 == (0 - 2)
@test (-0 == 0)
@test (-(-2) == 2)
@test -2 == (0 - 2)
end

function test_no_overflow(self::UnaryOpTestCase)
nines = repeat("9",32)
@test eval("+" * nines) == (10^32 - 1)
@test eval("-" * nines) == -(10^32 - 1)
@test eval("~" * nines) == ~(10^32 - 1)
end

function test_negation_of_exponentiation(self::UnaryOpTestCase)
@test (-(2^3) == -8)
@test (-2^3 == -8)
@test (-(2^4) == -16)
@test (-2^4 == 16)
end

function test_bad_types(self::UnaryOpTestCase)
for op in ("+", "-", "~")
@test_throws TypeError eval(op + "b\'a\'")
@test_throws TypeError eval(op + "\'a\'")
end
@test_throws TypeError eval("~2j")
@test_throws TypeError eval("~2.0")
end

function main()
unary_op_test_case = UnaryOpTestCase()
test_negative(unary_op_test_case)
test_positive(unary_op_test_case)
test_invert(unary_op_test_case)
test_no_overflow(unary_op_test_case)
test_negation_of_exponentiation(unary_op_test_case)
test_bad_types(unary_op_test_case)
end

main()