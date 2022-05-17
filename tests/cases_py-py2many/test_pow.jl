using Test


abstract type AbstractPowTest end
abstract type AbstractTestRpow end
mutable struct PowTest <: AbstractPowTest

end
function powtest(self::PowTest, type_)
if type_ != float
for i in -1000:999
@test (pow(type_(i), 0) == 1)
@test (pow(type_(i), 1) == type_(i))
@test (pow(type_(0), 1) == type_(0))
@test (pow(type_(1), 1) == type_(1))
end
for i in -100:99
@test (pow(type_(i), 3) == i*i*i)
end
pow2 = 1
for i in 0:30
@test (pow(2, i) == pow2)
if i != 30
pow2 = pow2*2
end
end
for othertype in (int,)
for i in append!(collect(-10:-1), collect(1:9))
ii = type_(i)
for j in 1:10
jj = -othertype(j)
pow(ii, jj)
end
end
end
end
for othertype in (int, float)
for i in 1:99
zero = type_(0)
exp = -othertype(i / 10.0)
if exp == 0
continue;
end
@test_throws ZeroDivisionError pow(zero, exp)
end
end
il, ih = (-20, 20)
jl, jh = (-5, 5)
kl, kh = (-10, 10)
asseq = self.assertEqual
if type_ == float
il = 1
asseq = self.assertAlmostEqual
elseif type_ == int
jl = 0
elseif type_ == int
jl, jh = (0, 15)
end
for i in il:ih
for j in jl:jh
for k in kl:kh
if k != 0
if type_ == float || j < 0
@test_throws TypeError pow(type_(i), j, k)
continue;
end
asseq(pow(type_(i), j, k), pow(type_(i), j) % type_(k))
end
end
end
end
end

function test_powint(self::PowTest)
powtest(self, int)
end

function test_powfloat(self::PowTest)
powtest(self, float)
end

function test_other(self::PowTest)
@test (pow(3, 3) % 8 == pow(3, 3, 8))
@test (pow(3, 3) % -8 == pow(3, 3, -8))
@test (pow(3, 2) % -2 == pow(3, 2, -2))
@test (pow(-3, 3) % 8 == pow(-3, 3, 8))
@test (pow(-3, 3) % -8 == pow(-3, 3, -8))
@test (pow(5, 2) % -8 == pow(5, 2, -8))
@test (pow(3, 3) % 8 == pow(3, 3, 8))
@test (pow(3, 3) % -8 == pow(3, 3, -8))
@test (pow(3, 2) % -2 == pow(3, 2, -2))
@test (pow(-3, 3) % 8 == pow(-3, 3, 8))
@test (pow(-3, 3) % -8 == pow(-3, 3, -8))
@test (pow(5, 2) % -8 == pow(5, 2, -8))
for i in -10:10
for j in 0:5
for k in -7:10
if j >= 0 && k != 0
@test (pow(i, j) % k == pow(i, j, k))
end
if j >= 0 && k != 0
@test (pow(parse(Int, i), j) % k == pow(parse(Int, i), j, k))
end
end
end
end
end

function test_bug643260(self::TestRpow)
mutable struct TestRpow <: AbstractTestRpow

end
function __rpow__(self::TestRpow, other)
return nothing
end

nothing^TestRpow()
end

function test_bug705231(self::PowTest)
eq = self.assertEqual
a = -1.0
eq(pow(a, 1.23e+167), 1.0)
eq(pow(a, -1.23e+167), 1.0)
for b in -10:10
eq(pow(a, float(b)), b & 1 && -1.0 || 1.0)
end
for n in 0:99
fiveto = float(5^n)
expected = fiveto % 2.0 && -1.0 || 1.0
eq(pow(a, fiveto), expected)
eq(pow(a, -(fiveto)), expected)
end
eq(expected, 1.0)
end

function test_negative_exponent(self::PowTest)
for a in -50:49
for m in -50:49
subTest(self, a, m) do 
if m != 0 && gcd(math, a, m) == 1
inv = pow(a, -1, m)
@test (inv == inv % m)
@test ((inv*a - 1) % m == 0)
@test (pow(a, -2, m) == pow(inv, 2, m))
@test (pow(a, -3, m) == pow(inv, 3, m))
@test (pow(a, -1001, m) == pow(inv, 1001, m))
else
assertRaises(self, ValueError) do 
pow(a, -1, m)
end
assertRaises(self, ValueError) do 
pow(a, -2, m)
end
assertRaises(self, ValueError) do 
pow(a, -1001, m)
end
end
end
end
end
end

function main()
pow_test = PowTest()
powtest(pow_test)
test_powint(pow_test)
test_powfloat(pow_test)
test_other(pow_test)
test_bug643260(pow_test)
test_bug705231(pow_test)
test_negative_exponent(pow_test)
end

main()