using Test

import random



using decimal: Decimal
using fractions: Fraction
abstract type AbstractHashTest end
abstract type AbstractHalibutProxy end
abstract type AbstractComparisonTest end
_PyHASH_MODULUS = sys.hash_info.modulus
_PyHASH_INF = sys.hash_info.inf
mutable struct HashTest <: AbstractHashTest

end
function check_equal_hash(self::HashTest, x, y)
@test (hash(x) == hash(y))
@test (x == y)
end

function test_bools(self::HashTest)
check_equal_hash(self, false, 0)
check_equal_hash(self, true, 1)
end

function test_integers(self::HashTest)
for i in -1000:999
check_equal_hash(self, i, float(i))
check_equal_hash(self, i, D(i))
check_equal_hash(self, i, F(i))
end
for i in 0:99
n = 2^i - 1
if n == Int(floor(float(n)))
check_equal_hash(self, n, float(n))
check_equal_hash(self, -(n), -float(n))
end
check_equal_hash(self, n, D(n))
check_equal_hash(self, n, F(n))
check_equal_hash(self, -(n), D(-(n)))
check_equal_hash(self, -(n), F(-(n)))
n = 2^i
check_equal_hash(self, n, float(n))
check_equal_hash(self, -(n), -float(n))
check_equal_hash(self, n, D(n))
check_equal_hash(self, n, F(n))
check_equal_hash(self, -(n), D(-(n)))
check_equal_hash(self, -(n), F(-(n)))
end
for _ in 0:999
e = randrange(random, 300)
n = randrange(random, -(10^e), 10^e)
check_equal_hash(self, n, D(n))
check_equal_hash(self, n, F(n))
if n == Int(floor(float(n)))
check_equal_hash(self, n, float(n))
end
end
end

function test_binary_floats(self::HashTest)
check_equal_hash(self, 0.0, -0.0)
check_equal_hash(self, 0.0, D(0))
check_equal_hash(self, -0.0, D(0))
check_equal_hash(self, -0.0, D("-0.0"))
check_equal_hash(self, 0.0, F(0))
check_equal_hash(self, float("inf"), D("inf"))
check_equal_hash(self, float("-inf"), D("-inf"))
for _ in 0:999
x = pylib::random::random()*exp(math, pylib::random::random()*200.0 - 100.0)
check_equal_hash(self, x, from_float(D, x))
check_equal_hash(self, x, from_float(F, x))
end
end

function test_complex(self::HashTest)
test_values = [0.0, -0.0, 1.0, -1.0, 0.40625, -5136.5, float("inf"), float("-inf")]
for zero in (-0.0, 0.0)
for value in test_values
check_equal_hash(self, value, complex(value, zero))
end
end
end

function test_decimals(self::HashTest)
zeros = ["0", "-0", "0.0", "-0.0e10", "000e-10"]
for zero in zeros
check_equal_hash(self, D(zero), D(0))
end
check_equal_hash(self, D("1.00"), D(1))
check_equal_hash(self, D("1.00000"), D(1))
check_equal_hash(self, D("-1.00"), D(-1))
check_equal_hash(self, D("-1.00000"), D(-1))
check_equal_hash(self, D("123e2"), D(12300))
check_equal_hash(self, D("1230e1"), D(12300))
check_equal_hash(self, D("12300"), D(12300))
check_equal_hash(self, D("12300.0"), D(12300))
check_equal_hash(self, D("12300.00"), D(12300))
check_equal_hash(self, D("12300.000"), D(12300))
end

function test_fractions(self::HashTest)
@test (hash(F(1, _PyHASH_MODULUS)) == _PyHASH_INF)
@test (hash(F(-1, 3*_PyHASH_MODULUS)) == -(_PyHASH_INF))
@test (hash(F(7*_PyHASH_MODULUS, 1)) == 0)
@test (hash(F(-(_PyHASH_MODULUS), 1)) == 0)
end

function test_hash_normalization(self::HalibutProxy)
mutable struct HalibutProxy <: AbstractHalibutProxy

end
function __hash__(self::HalibutProxy)
return hash("halibut")
end

function __eq__(self::HalibutProxy, other)::Bool
return other == "halibut"
end

x = Set(["halibut", HalibutProxy()])
assertEqual(self, length(x), 1)
end

mutable struct ComparisonTest <: AbstractComparisonTest

end
function test_mixed_comparisons(self::ComparisonTest)
test_values = [float("-inf"), D("-1e425000000"), -1e+308, F(-22, 7), -3.14, -2, 0.0, 1e-320, true, F("1.2"), D("1.3"), float("1.4"), F(275807, 195025), D("1.414213562373095048801688724"), F(114243, 80782), F(473596569, 84615), 7e+200, D("infinity")]
for (i, first) in enumerate(test_values)
for second in test_values[i + 2:end]
assertLess(self, first, second)
assertLessEqual(self, first, second)
assertGreater(self, second, first)
assertGreaterEqual(self, second, first)
end
end
end

function test_complex(self::ComparisonTest)
z = 1.0 + 0im
w = -3.14 + 2.7im
for v in (1, 1.0, F(1), D(1), complex(1))
@test (z == v)
@test (v == z)
end
for v in (2, 2.0, F(2), D(2), complex(2))
assertNotEqual(self, z, v)
assertNotEqual(self, v, z)
assertNotEqual(self, w, v)
assertNotEqual(self, v, w)
end
for v in (1, 1.0, F(1), D(1), complex(1), 2, 2.0, F(2), D(2), complex(2), w)
for op in (operator.le, operator.lt, operator.ge, operator.gt)
@test_throws TypeError op(z, v)
@test_throws TypeError op(v, z)
end
end
end

function main()
hash_test = HashTest()
check_equal_hash(hash_test)
test_bools(hash_test)
test_integers(hash_test)
test_binary_floats(hash_test)
test_complex(hash_test)
test_decimals(hash_test)
test_fractions(hash_test)
test_hash_normalization(hash_test)
comparison_test = ComparisonTest()
test_mixed_comparisons(comparison_test)
test_complex(comparison_test)
end

main()