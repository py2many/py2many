# Taken from CPython.

import math

eps = 1E-05
NAN = float('nan')
INF = float('inf')
NINF = float('-inf')
FLOAT_MAX = 1.7976931348623157e+308 # sys.float_info.max
FLOAT_MIN = 2.2250738585072014e-308 # sys.float_info.min

def count_set_bits(n):
    """Number of '1' bits in binary expansion of a nonnnegative integer."""
    return 1 + count_set_bits(n & n - 1) if n else 0

def partial_product(start, stop):
    """Product of integers in range(start, stop, 2), computed recursively.
    start and stop should both be odd, with start <= stop.
    """
    numfactors = (stop - start) >> 1
    if not numfactors:
        return 1
    elif numfactors == 1:
        return start
    else:
        mid = (start + numfactors) | 1
        return partial_product(start, mid) * partial_product(mid, stop)

def py_factorial(n):
    """Factorial of nonnegative integer n, via "Binary Split Factorial Formula"
    described at http://www.luschny.de/math/factorial/binarysplitfact.html
    """
    inner = outer = 1
    for i in reversed(range(n.bit_length())):
        inner *= partial_product((n >> i + 1) + 1 | 1, (n >> i) + 1 | 1)
        outer *= inner
    return outer << (n - count_set_bits(n))

def ftest(got, expected):
    return abs(got - expected) < 1e-10

def testConstants():
    # Ref: Abramowitz & Stegun (Dover, 1965)
    assert ftest(math.pi, 3.141592653589793238462643)
    assert ftest(math.e, 2.718281828459045235360287)
    assert math.tau == 2*math.pi

def testAcos():
    assert ftest(math.acos(-1), math.pi)
    assert ftest(math.acos(0), math.pi/2)
    assert ftest(math.acos(1), 0)
    assert math.isnan(math.acos(NAN))

def testAcosh():
    assert ftest(math.acosh(1), 0)
    assert ftest(math.acosh(2), 1.3169578969248168)
    assert math.acosh(INF) == INF
    assert math.isnan(math.acosh(NAN))

def testAsin():
    assert ftest(math.asin(-1), -math.pi/2)
    assert ftest(math.asin(0), 0)
    assert ftest(math.asin(1), math.pi/2)
    assert math.isnan(math.asin(NAN))

def testAsinh():
    assert ftest(math.asinh(0), 0)
    assert ftest(math.asinh(1), 0.88137358701954305)
    assert ftest(math.asinh(-1), -0.88137358701954305)
    assert math.asinh(INF) == INF
    assert math.asinh(NINF) == NINF
    assert math.isnan(math.asinh(NAN))

def testAtan():
    assert ftest(math.atan(-1), -math.pi/4)
    assert ftest(math.atan(0), 0)
    assert ftest(math.atan(1), math.pi/4)
    assert ftest(math.atan(INF), math.pi/2)
    assert ftest(math.atan(NINF), -math.pi/2)
    assert math.isnan(math.atan(NAN))

def testAtanh():
    assert ftest(math.atanh(0), 0)
    assert ftest(math.atanh(0.5), 0.54930614433405489)
    assert ftest(math.atanh(-0.5), -0.54930614433405489)
    assert math.isnan(math.atanh(NAN))

def testAtan2():
    assert ftest(math.atan2(-1, 0), -math.pi/2)
    assert ftest(math.atan2(-1, 1), -math.pi/4)
    assert ftest(math.atan2(0, 1), 0)
    assert ftest(math.atan2(1, 1), math.pi/4)
    assert ftest(math.atan2(1, 0), math.pi/2)

    # math.atan2(0, x)
    assert ftest(math.atan2(0., NINF), math.pi)
    assert ftest(math.atan2(0., -2.3), math.pi)
    assert ftest(math.atan2(0., -0.), math.pi)
    assert math.atan2(0., 0.) == 0.
    assert math.atan2(0., 2.3) == 0.
    assert math.atan2(0., INF) == 0.
    assert math.isnan(math.atan2(0., NAN))
    # math.atan2(-0, x)
    assert ftest(math.atan2(-0., NINF), -math.pi)
    assert ftest(math.atan2(-0., -2.3), -math.pi)
    assert ftest(math.atan2(-0., -0.), -math.pi)
    assert math.atan2(-0., 0.) == -0.
    assert math.atan2(-0., 2.3) == -0.
    assert math.atan2(-0., INF) == -0.
    assert math.isnan(math.atan2(-0., NAN))
    # math.atan2(INF, x)
    assert ftest(math.atan2(INF, NINF), math.pi*3/4)
    assert ftest(math.atan2(INF, -2.3), math.pi/2)
    assert ftest(math.atan2(INF, -0.0), math.pi/2)
    assert ftest(math.atan2(INF, 0.0), math.pi/2)
    assert ftest(math.atan2(INF, 2.3), math.pi/2)
    assert ftest(math.atan2(INF, INF), math.pi/4)
    assert math.isnan(math.atan2(INF, NAN))
    # math.atan2(NINF, x)
    assert ftest(math.atan2(NINF, NINF), -math.pi*3/4)
    assert ftest(math.atan2(NINF, -2.3), -math.pi/2)
    assert ftest(math.atan2(NINF, -0.0), -math.pi/2)
    assert ftest(math.atan2(NINF, 0.0), -math.pi/2)
    assert ftest(math.atan2(NINF, 2.3), -math.pi/2)
    assert ftest(math.atan2(NINF, INF), -math.pi/4)
    assert math.isnan(math.atan2(NINF, NAN))
    # math.atan2(+finite, x)
    assert ftest(math.atan2(2.3, NINF), math.pi)
    assert ftest(math.atan2(2.3, -0.), math.pi/2)
    assert ftest(math.atan2(2.3, 0.), math.pi/2)
    assert math.atan2(2.3, INF) == 0.
    assert math.isnan(math.atan2(2.3, NAN))
    # math.atan2(-finite, x)
    assert ftest(math.atan2(-2.3, NINF), -math.pi)
    assert ftest(math.atan2(-2.3, -0.), -math.pi/2)
    assert ftest(math.atan2(-2.3, 0.), -math.pi/2)
    assert math.atan2(-2.3, INF) == -0.
    assert math.isnan(math.atan2(-2.3, NAN))
    # math.atan2(NAN, x)
    assert math.isnan(math.atan2(NAN, NINF))
    assert math.isnan(math.atan2(NAN, -2.3))
    assert math.isnan(math.atan2(NAN, -0.))
    assert math.isnan(math.atan2(NAN, 0.))
    assert math.isnan(math.atan2(NAN, 2.3))
    assert math.isnan(math.atan2(NAN, INF))
    assert math.isnan(math.atan2(NAN, NAN))

# Python 3.11
def testCbrt():
    assert True
    #assert ftest(math.cbrt(0), 0)
    #assert ftest(math.cbrt(1), 1)
    #assert ftest(math.cbrt(8), 2)
    #assert ftest(math.cbrt(0.0), 0.0)
    #assert ftest(math.cbrt(-0.0), -0.0)
    #assert ftest(math.cbrt(1.2), 1.062658569182611)
    #assert ftest(math.cbrt(-2.6), -1.375068867074141)
    #assert ftest(math.cbrt(27), 3)
    #assert ftest(math.cbrt(-1), -1)
    #assert ftest(math.cbrt(-27), -3)
    #assert math.cbrt(INF) == INF
    #assert math.cbrt(NINF) == NINF
    #assert math.isnan(math.cbrt(NAN))

def testCeil():
    assert int == type(math.ceil(0.5))
    assert math.ceil(0.5) == 1
    assert math.ceil(1.0) == 1
    assert math.ceil(1.5) == 2
    assert math.ceil(-0.5) == 0
    assert math.ceil(-1.0) == -1
    assert math.ceil(-1.5) == -1
    assert math.ceil(0.0) == 0
    assert math.ceil(-0.0) == 0
    #assert math.ceil(INF) == INF
    #assert math.ceil(NINF) == NINF
    #assert math.isnan(math.ceil(NAN))

def testCopysign():
    assert math.copysign(1, 42) == 1.0
    assert math.copysign(0., 42) == 0.0
    assert math.copysign(1., -42) == -1.0
    assert math.copysign(3, 0.) == 3.0
    assert math.copysign(4., -0.) == -4.0

    # copysign should let us distinguish signs of zeros
    assert math.copysign(1., 0.) == 1.
    assert math.copysign(1., -0.) == -1.
    assert math.copysign(INF, 0.) == INF
    assert math.copysign(INF, -0.) == NINF
    assert math.copysign(NINF, 0.) == INF
    assert math.copysign(NINF, -0.) == NINF
    # and of infinities
    assert math.copysign(1., INF) == 1.
    assert math.copysign(1., NINF) == -1.
    assert math.copysign(INF, INF) == INF
    assert math.copysign(INF, NINF) == NINF
    assert math.copysign(NINF, INF) == INF
    assert math.copysign(NINF, NINF) == NINF
    assert math.isnan(math.copysign(NAN, 1.))
    assert math.isnan(math.copysign(NAN, INF))
    assert math.isnan(math.copysign(NAN, NINF))
    assert math.isnan(math.copysign(NAN, NAN))
    # copysign(INF, NAN) may be INF or it may be NINF, since
    # we don't know whether the sign bit of NAN is set on any
    # given platform.
    assert math.isinf(math.copysign(INF, NAN))
    # similarly, copysign(2., NAN) could be 2. or -2.
    assert abs(math.copysign(2., NAN)) == 2.

def testCos():
    assert ftest(math.cos(-math.pi/2), 0)
    assert ftest(math.cos(0), 1)
    assert ftest(math.cos(math.pi/2), 0)
    assert ftest(math.cos(math.pi), -1)
    assert math.isnan(math.cos(NAN))

def testCosh():
    assert ftest(math.cosh(0), 1)
    assert ftest(math.cosh(2)-2*math.cosh(1)**2, -1) # Thanks to Lambert
    assert math.cosh(INF) == INF
    assert math.cosh(NINF) == INF
    assert math.isnan(math.cosh(NAN))

def testDegrees():
    assert ftest(math.degrees(math.pi), 180.0)
    assert ftest(math.degrees(math.pi/2), 90.0)
    assert ftest(math.degrees(-math.pi/4), -45.0)
    assert ftest(math.degrees(0), 0)

def testExp():
    assert ftest(math.exp(-1), 1/math.e)
    assert ftest(math.exp(0), 1)
    assert ftest(math.exp(1), math.e)
    assert math.exp(INF) == INF
    assert math.exp(NINF) == 0.
    assert math.isnan(math.exp(NAN))

# Python 3.11
def testExp2():
    assert True
    #assert ftest(math.exp2(-1), 0.5)
    #assert ftest(math.exp2(0), 1)
    #assert ftest(math.exp2(1), 2)
    #assert ftest(math.exp2(2.3), 4.924577653379665)
    #assert math.exp2(INF) == INF
    #assert math.exp2(NINF) == 0.
    #assert math.isnan(math.exp2(NAN))

def testFabs():
    assert ftest(math.fabs(-1), 1)
    assert ftest(math.fabs(0), 0)
    assert ftest(math.fabs(1), 1)

def testFactorial():
    assert math.factorial(0) == 1
    total = 1
    for i in range(1, 1000):
        total *= i
        assert math.factorial(i) == total
        assert math.factorial(i) == py_factorial(i)

def testFloor():
    assert math.floor(0.5) == 0
    assert math.floor(1.0) == 1
    assert math.floor(1.5) == 1
    assert math.floor(-0.5) == -1
    assert math.floor(-1.0) == -1
    assert math.floor(-1.5) == -2
    #assert math.ceil(INF) == INF
    #assert math.ceil(NINF) == NINF
    #assert math.isnan(math.floor(NAN))

def testFmod():
    assert ftest(math.fmod(10, 1), 0.0)
    assert ftest(math.fmod(10, 0.5), 0.0)
    assert ftest(math.fmod(10, 1.5), 1.0)
    assert ftest(math.fmod(-10, 1), -0.0)
    assert ftest(math.fmod(-10, 0.5), -0.0)
    assert ftest(math.fmod(-10, 1.5), -1.0)
    assert math.isnan(math.fmod(NAN, 1.))
    assert math.isnan(math.fmod(1., NAN))
    assert math.isnan(math.fmod(NAN, NAN))
    assert math.fmod(3.0, INF) == 3.0
    assert math.fmod(-3.0, INF) == -3.0
    assert math.fmod(3.0, NINF) == 3.0
    assert math.fmod(-3.0, NINF) == -3.0
    assert math.fmod(0.0, 3.0) == 0.0
    assert math.fmod(0.0, NINF) == 0.0

def testfrexp(result, expected):
    (mant, exp), (emant, eexp) = result, expected
    if abs(mant-emant) > eps or exp != eexp:
        assert False

def testFrexp():
    testfrexp(math.frexp(-1), (-0.5, 1))
    testfrexp(math.frexp(0), (0, 0))
    testfrexp(math.frexp(1), (0.5, 1))
    testfrexp(math.frexp(2), (0.5, 2))

    assert math.frexp(INF)[0] == INF
    assert math.frexp(NINF)[0] == NINF
    assert math.isnan(math.frexp(NAN)[0])

# Too complicated for backend right now.
def testFsum():
    """
    # math.fsum relies on exact rounding for correct operation.
    # There's a known problem with IA32 floating-point that causes
    # inexact rounding in some situations, and will cause the
    # math.fsum tests below to fail; see issue #2937.  On non IEEE
    # 754 platforms, and on IEEE 754 platforms that exhibit the
    # problem described in issue #2937, we simply skip the whole
    # test.

    # Python version of math.fsum, for comparison.  Uses a
    # different algorithm based on frexp, ldexp and integer
    # arithmetic.
    from sys import float_info
    mant_dig = float_info.mant_dig
    etiny = float_info.min_exp - mant_dig

    def msum(iterable):
        Full precision summation.  Compute sum(iterable) without any
        intermediate accumulation of error.  Based on the 'lsum' function
        at http://code.activestate.com/recipes/393090/
        tmant, texp = 0, 0
        for x in iterable:
            mant, exp = math.frexp(x)
            mant, exp = int(math.ldexp(mant, mant_dig)), exp - mant_dig
            if texp > exp:
                tmant <<= texp-exp
                texp = exp
            else:
                mant <<= exp-texp
            tmant += mant
        # Round tmant * 2**texp to a float.  The original recipe
        # used float(str(tmant)) * 2.0**texp for this, but that's
        # a little unsafe because str -> float conversion can't be
        # relied upon to do correct rounding on all platforms.
        tail = max(len(bin(abs(tmant)))-2 - mant_dig, etiny - texp)
        if tail > 0:
            h = 1 << (tail-1)
            tmant = tmant // (2*h) + bool(tmant & h and tmant & 3*h-1)
            texp += tail
        return math.ldexp(tmant, texp)

    test_values = [
        ([], 0.0),
        ([0.0], 0.0),
        ([1e100, 1.0, -1e100, 1e-100, 1e50, -1.0, -1e50], 1e-100),
        ([2.0**53, -0.5, -2.0**-54], 2.0**53-1.0),
        ([2.0**53, 1.0, 2.0**-100], 2.0**53+2.0),
        ([2.0**53+10.0, 1.0, 2.0**-100], 2.0**53+12.0),
        ([2.0**53-4.0, 0.5, 2.0**-54], 2.0**53-3.0),
        ([1./n for n in range(1, 1001)],
            float.fromhex('0x1.df11f45f4e61ap+2')),
        ([(-1.)**n/n for n in range(1, 1001)],
            float.fromhex('-0x1.62a2af1bd3624p-1')),
        ([1e16, 1., 1e-16], 10000000000000002.0),
        ([1e16-2., 1.-2.**-53, -(1e16-2.), -(1.-2.**-53)], 0.0),
        # exercise code for resizing partials array
        ([2.**n - 2.**(n+50) + 2.**(n+52) for n in range(-1074, 972, 2)] +
            [-2.**1022],
            float.fromhex('0x1.5555555555555p+970')),
        ]

    # Telescoping sum, with exact differences (due to Sterbenz)
    terms = [1.7**i for i in range(1001)]
    test_values.append((
        [terms[i+1] - terms[i] for i in range(1000)] + [-terms[1000]],
        -terms[0]
    ))

    for i, (vals, expected) in enumerate(test_values):
        assert math.fsum(vals) == expected

    from random import random, gauss, shuffle
    for j in range(1000):
        vals = [7, 1e100, -7, -1e100, -9e-20, 8e-20] * 10
        s = 0
        for i in range(200):
            v = gauss(0, random()) ** 7 - s
            s += v
            vals.append(v)
        shuffle(vals)

        s = msum(vals)
        assert msum(vals) == math.fsum(vals)"""

def testGcd():
    assert math.gcd(0, 0) == 0
    assert math.gcd(1, 0) == 1
    assert math.gcd(-1, 0) == 1
    assert math.gcd(0, 1) == 1
    assert math.gcd(0, -1) == 1
    assert math.gcd(7, 1) == 1
    assert math.gcd(7, -1) == 1
    assert math.gcd(-23, 15) == 1
    assert math.gcd(120, 84) == 12
    assert math.gcd(84, -120) == 12
    assert math.gcd(1216342683557601535506311712, 436522681849110124616458784) == 32

    x = 434610456570399902378880679233098819019853229470286994367836600566
    y = 1064502245825115327754847244914921553977
    for c in (652560,
                576559230871654959816130551884856912003141446781646602790216406874):
        a = x * c
        b = y * c
        assert math.gcd(a, b) == c
        assert math.gcd(b, a) == c
        assert math.gcd(-a, b) == c
        assert math.gcd(b, -a) == c
        assert math.gcd(a, -b) == c
        assert math.gcd(-b, a) == c
        assert math.gcd(-a, -b) == c
        assert math.gcd(-b, -a) == c

    assert math.gcd() == 0
    assert math.gcd(120) == 120
    assert math.gcd(-120) == 120
    assert math.gcd(120, 84, 102) == 6
    assert math.gcd(120, 1, 84) == 1

def testHypot():
    # Test different numbers of arguments (from zero to five)
    # against a straightforward pure python implementation
    args = math.e, math.pi, math.sqrt(2.0), math.gamma(3.5), math.sin(2.1)
    for i in range(len(args)+1):
        assert abs(math.hypot(*args[:i]) - math.sqrt(sum(s**2 for s in args[:i]))) < 1e-6

    # Test allowable types (those with __float__)
    assert math.hypot(12.0, 5.0) == 13.0
    assert math.hypot(12, 5) == 13
    assert math.hypot(bool(1), bool(0), bool(1), bool(1)) == math.sqrt(3)

    # Test corner cases
    assert math.hypot(0.0, 0.0) == 0.0     # Max input is zero
    assert math.hypot(-10.5) == 10.5       # Negative input
    assert math.hypot() == 0.0             # Negative input
    assert 1.0 == math.copysign(1.0, math.hypot(-0.0))        # Convert negative zero to positive zero
    assert math.hypot(1.5, 1.5, 0.5) == math.hypot(1.5, 0.5, 1.5) # Handling of moving max to the end

    # Any infinity gives positive infinity.
    assert math.hypot(INF) == INF
    assert math.hypot(0, INF) == INF
    assert math.hypot(10, INF) == INF
    assert math.hypot(-10, INF) == INF
    assert math.hypot(NAN, INF) == INF
    assert math.hypot(INF, NAN) == INF
    assert math.hypot(NINF, NAN) == INF
    assert math.hypot(NAN, NINF) == INF
    assert math.hypot(-INF, INF) == INF
    assert math.hypot(-INF, -INF) == INF
    assert math.hypot(10, -INF) == INF

    # If no infinity, any NaN gives a NaN.
    assert math.isnan(math.hypot(NAN))
    assert math.isnan(math.hypot(0, NAN))
    assert math.isnan(math.hypot(NAN, 10))
    assert math.isnan(math.hypot(10, NAN))
    assert math.isnan(math.hypot(NAN, NAN))
    assert math.isnan(math.hypot(NAN))

    # Verify scaling for extremely large values
    fourthmax = FLOAT_MAX / 4.0
    for n in range(32):
        assert math.isclose(math.hypot(*([fourthmax]*n)),
                                        fourthmax * math.sqrt(n))

    # Verify scaling for extremely small values
    for exp in range(32):
        scale = FLOAT_MIN / 2.0 ** exp
        assert math.hypot(4*scale, 3*scale) == 5*scale


# Taken from itertools documentation.
def product(values: list[float], repeat: int) -> list[float]:
    # product('ABCD', 'xy') --> Ax Ay Bx By Cx Cy Dx Dy
    # product(range(2), repeat=3) --> 000 001 010 011 100 101 110 111
    pools = [values] * repeat
    result = [[]]
    for pool in pools:
        result = [x+[y] for x in result for y in pool]
    for prod in result:
        yield tuple(prod)


def testDist():
    # Simple exact cases
    assert math.dist((1.0, 2.0, 3.0), (4.0, 2.0, -1.0)) == 5.0
    assert math.dist((1, 2, 3), (4, 2, -1)) == 5.0

    # Test different numbers of arguments (from zero to nine)
    # against a straightforward pure python implementation
    #for i in range(9):
    #    for j in range(5):
    #        p = tuple(random.uniform(-5, 5) for k in range(i))
    #        q = tuple(random.uniform(-5, 5) for k in range(i))
    #        assert abs(math.dist(p, q) - math.sqrt(sum((px - qx) ** 2.0 for px, qx in zip(p, q)))) < 1e-6

    # Test non-tuple inputs
    assert math.dist([1.0, 2.0, 3.0], [4.0, 2.0, -1.0]) == 5.0
    # assert math.dist(iter([1.0, 2.0, 3.0]), iter([4.0, 2.0, -1.0])) == 5.0

    # Test allowable types (those with __float__)
    assert math.dist((14.0, 1.0), (2.0, -4.0)) == 13.0
    assert math.dist((14, 1), (2, -4)) == 13

    # Test corner cases
    assert math.dist((13.25, 12.5, -3.25), (13.25, 12.5, -3.25)) == 0.0  # distance with self is zero
    assert math.dist((), ()) == 0.0 # Zero-dimensional case
    assert 1.0 == math.copysign(1.0, math.dist((-0.0,), (0.0,))) # Convert negative zero to positive zero
    assert 1.0 == math.copysign(1.0, math.dist((0.0,), (-0.0,))) # Convert negative zero to positive zero
    assert math.dist((1.5, 1.5, 0.5), (0, 0, 0)) == math.dist((1.5, 0.5, 1.5), (0, 0, 0)) # Handling of moving max to the end

    # Verify that the one dimensional case is equivalent to abs()
    #for i in range(20):
    #    p, q = random.random(), random.random()
    #    assert math.dist((p,), (q,)) == abs(p - q)

    # Test special values
    values = [NINF, -10.5, -0.0, 0.0, 10.5, INF, NAN]
    for p in product(values, 3):
        for q in product(values, 3):
            diffs = [px - qx for px, qx in zip(p, q)]
            if any(map(math.isinf, diffs)):
                # Any infinite difference gives positive infinity.
                assert math.dist(p, q) == INF
            elif any(map(math.isnan, diffs)):
                # If no infinity, any NaN gives a NaN.
                assert math.isnan(math.dist(p, q))

    # Verify scaling for extremely large values
    fourthmax = FLOAT_MAX / 4.0
    for n in range(32):
        p = (fourthmax,) * n
        q = (0.0,) * n
        assert math.isclose(math.dist(p, q), fourthmax * math.sqrt(n))
        assert math.isclose(math.dist(q, p), fourthmax * math.sqrt(n))

    # Verify scaling for extremely small values
    for exp in range(32):
        scale = FLOAT_MIN / 2.0 ** exp
        p = (4*scale, 3*scale)
        q = (0.0, 0.0)
        assert math.dist(p, q) == 5*scale
        assert math.dist(q, p) == 5*scale

def testIsqrt():
    # Test a variety of inputs, large and small.
    test_values = (
        list(range(1000))
        + list(range(10**6 - 1000, 10**6 + 1000))
        + [2**e + i for e in range(60, 200) for i in range(-40, 40)]
        + [3**9999, 10**5001]
    )

    for value in test_values:
            s = math.isqrt(value)
            assert s*s <= value
            assert value < (s+1)*(s+1)

    # Integer-like things
    s = math.isqrt(True)
    assert s == 1

    s = math.isqrt(False)
    assert s == 0

def test_lcm():
    lcm = math.lcm
    assert lcm(0, 0) == 0
    assert lcm(1, 0) == 0
    assert lcm(-1, 0) == 0
    assert lcm(0, 1) == 0
    assert lcm(0, -1) == 0
    assert lcm(7, 1) == 7
    assert lcm(7, -1) == 7
    assert lcm(-23, 15) == 345
    assert lcm(120, 84) == 840
    assert lcm(84, -120) == 840
    assert lcm(1216342683557601535506311712, 436522681849110124616458784) == 16592536571065866494401400422922201534178938447014944

    x = 43461045657039990237
    y = 10645022458251153277
    for c in (652560,
                57655923087165495981):
        a = x * c
        b = y * c
        d = x * y * c
        assert lcm(a, b) == d
        assert lcm(b, a) == d
        assert lcm(-a, b) == d
        assert lcm(b, -a) == d
        assert lcm(a, -b) == d
        assert lcm(-b, a) == d
        assert lcm(-a, -b) == d
        assert lcm(-b, -a) == d

    assert lcm() == 1
    assert lcm(120) == 120
    assert lcm(-120) == 120
    assert lcm(120, 84, 102) == 14280
    assert lcm(120, 0, 84) == 0

def testLdexp():
    assert ftest(math.ldexp(0,1), 0)
    assert ftest(math.ldexp(1,1), 2)
    assert ftest(math.ldexp(1,-1), 0.5)
    assert ftest(math.ldexp(-1,1), -2)
    assert math.ldexp(1., -1000000) == 0.
    assert math.ldexp(-1., -1000000) == -0.
    assert math.ldexp(INF, 30) == INF
    assert math.ldexp(NINF, -213) == NINF
    assert math.isnan(math.ldexp(NAN, 0))

    # large second argument
    for n in [10**5, 10**10, 10**20, 10**40]:
        assert math.ldexp(INF, -n) == INF
        assert math.ldexp(NINF, -n) == NINF
        assert math.ldexp(1., -n) == 0.
        assert math.ldexp(-1., -n) == -0.
        assert math.ldexp(0., -n) == 0.
        assert math.ldexp(-0., -n) == -0.
        assert math.isnan(math.ldexp(NAN, -n))

        assert math.ldexp(0., n) == 0.
        assert math.ldexp(-0., n) == -0.
        assert math.ldexp(INF, n) == INF
        assert math.ldexp(NINF, n) == NINF
        assert math.isnan(math.ldexp(NAN, n))

def testLog():
    assert ftest(math.log(1/math.e), -1)
    assert ftest(math.log(1), 0)
    assert ftest(math.log(math.e), 1)
    assert ftest(math.log(32,2), 5)
    assert ftest(math.log(10**40, 10), 40)
    assert ftest(math.log(10**40, 10**20), 2)
    assert ftest(math.log(10**1000), 2302.5850929940457)
    assert math.log(INF) == INF
    assert math.isnan(math.log(NAN))

def testLog1p():
    for n in [2, 2**90, 2**300]:
        assert abs(math.log1p(n) - math.log1p(float(n))) < 1e-6
    assert math.log1p(INF) == INF

def testLog2():

    # Check some integer values
    assert math.log2(1) == 0.0
    assert math.log2(2) == 1.0
    assert math.log2(4) == 2.0

    # Large integer values
    assert math.log2(2**1023) == 1023.0
    assert math.log2(2**1024) == 1024.0
    assert math.log2(2**2000) == 2000.0

    assert math.isnan(math.log2(NAN))

# log2() is not accurate enough on Mac OS X Tiger (10.4)
def testLog2Exact():
    # Check that we get exact equality for log2 of powers of 2.
    actual = [math.log2(math.ldexp(1.0, n)) for n in range(-1074, 1024)]
    expected = [float(n) for n in range(-1074, 1024)]
    assert actual == expected

def testLog10():
    assert ftest(math.log10(0.1), -1)
    assert ftest(math.log10(1), 0)
    assert ftest(math.log10(10), 1)
    assert ftest(math.log10(10**1000), 1000.0)
    assert math.log(INF) == INF
    assert math.isnan(math.log10(NAN))

def testmodf(result, expected):
    (v1, v2), (e1, e2) = result, expected
    if abs(v1-e1) > eps or abs(v2-e2):
        assert False

def testModf():
    testmodf(math.modf(1.5), (0.5, 1.0))
    testmodf(math.modf(-1.5), (-0.5, -1.0))

    assert math.modf(INF), (0.0 == INF)
    assert math.modf(NINF), (-0.0 == NINF)

    modf_nan = math.modf(NAN)
    assert math.isnan(modf_nan[0])
    assert math.isnan(modf_nan[1])

def testPow():
    assert ftest(math.pow(0,1), 0)
    assert ftest(math.pow(1,0), 1)
    assert ftest(math.pow(2,1), 2)
    assert ftest(math.pow(2,-1), 0.5)
    assert math.pow(INF, 1) == INF
    assert math.pow(NINF, 1) == NINF
    assert (math.pow(1, INF)) == 1.
    assert (math.pow(1, NINF)) == 1.
    assert math.isnan(math.pow(NAN, 1))
    assert math.isnan(math.pow(2, NAN))
    assert math.isnan(math.pow(0, NAN))
    assert math.pow(1, NAN) == 1

    # pow(0., x)
    assert math.pow(0., INF) == 0.
    assert math.pow(0., 3.) == 0.
    assert math.pow(0., 2.3) == 0.
    assert math.pow(0., 2.) == 0.
    assert math.pow(0., 0.) == 1.
    assert math.pow(0., -0.) == 1.
    assert math.isnan(math.pow(0., NAN))

    # pow(INF, x)
    assert math.pow(INF, INF) == INF
    assert math.pow(INF, 3.) == INF
    assert math.pow(INF, 2.3) == INF
    assert math.pow(INF, 2.) == INF
    assert math.pow(INF, 0.) == 1.
    assert math.pow(INF, -0.) == 1.
    assert math.pow(INF, -2.) == 0.
    assert math.pow(INF, -2.3) == 0.
    assert math.pow(INF, -3.) == 0.
    assert math.pow(INF, NINF) == 0.
    assert math.isnan(math.pow(INF, NAN))

    # pow(-0., x)
    assert math.pow(-0., INF) == 0.
    assert math.pow(-0., 3.) == -0.
    assert math.pow(-0., 2.3) == 0.
    assert math.pow(-0., 2.) == 0.
    assert math.pow(-0., 0.) == 1.
    assert math.pow(-0., -0.) == 1.
    assert math.isnan(math.pow(-0., NAN))

    # pow(NINF, x)
    assert math.pow(NINF, INF) == INF
    assert math.pow(NINF, 3.) == NINF
    assert math.pow(NINF, 2.3) == INF
    assert math.pow(NINF, 2.) == INF
    assert math.pow(NINF, 0.) == 1.
    assert math.pow(NINF, -0.) == 1.
    assert math.pow(NINF, -2.) == 0.
    assert math.pow(NINF, -2.3) == 0.
    assert math.pow(NINF, -3.) == -0.
    assert math.pow(NINF, NINF) == 0.
    assert math.isnan(math.pow(NINF, NAN))

    # pow(-1, x)
    assert math.pow(-1., INF) == 1.
    assert math.pow(-1., 3.) == -1.
    assert math.pow(-1., 2.) == 1.
    assert math.pow(-1., 0.) == 1.
    assert math.pow(-1., -0.) == 1.
    assert math.pow(-1., -2.) == 1.
    assert math.pow(-1., -3.) == -1.
    assert math.pow(-1., NINF) == 1.
    assert math.isnan(math.pow(-1., NAN))

    # pow(1, x)
    assert math.pow(1., INF) == 1.
    assert math.pow(1., 3.) == 1.
    assert math.pow(1., 2.3) == 1.
    assert math.pow(1., 2.) == 1.
    assert math.pow(1., 0.) == 1.
    assert math.pow(1., -0.) == 1.
    assert math.pow(1., -2.) == 1.
    assert math.pow(1., -2.3) == 1.
    assert math.pow(1., -3.) == 1.
    assert math.pow(1., NINF) == 1.
    assert math.pow(1., NAN) == 1.

    # pow(x, 0) should be 1 for any x
    assert math.pow(2.3, 0.) == 1.
    assert math.pow(-2.3, 0.) == 1.
    assert math.pow(NAN, 0.) == 1.
    assert math.pow(2.3, -0.) == 1.
    assert math.pow(-2.3, -0.) == 1.
    assert math.pow(NAN, -0.) == 1.

    # pow(x, y) is invalid if x is negative and y is not integral

    # pow(x, NINF)
    assert math.pow(1.9, NINF) == 0.
    assert math.pow(1.1, NINF) == 0.
    assert math.pow(0.9, NINF) == INF
    assert math.pow(0.1, NINF) == INF
    assert math.pow(-0.1, NINF) == INF
    assert math.pow(-0.9, NINF) == INF
    assert math.pow(-1.1, NINF) == 0.
    assert math.pow(-1.9, NINF) == 0.

    # pow(x, INF)
    assert math.pow(1.9, INF) == INF
    assert math.pow(1.1, INF) == INF
    assert math.pow(0.9, INF) == 0.
    assert math.pow(0.1, INF) == 0.
    assert math.pow(-0.1, INF) == 0.
    assert math.pow(-0.9, INF) == 0.
    assert math.pow(-1.1, INF) == INF
    assert math.pow(-1.9, INF) == INF

    # pow(x, y) should work for x negative, y an integer
    assert ftest(math.pow(-2.0, 3.0), -8.0)
    assert ftest(math.pow(-2.0, 2.0), 4.0)
    assert ftest(math.pow(-2.0, 1.0), -2.0)
    assert ftest(math.pow(-2.0, 0.0), 1.0)
    assert ftest(math.pow(-2.0, -0.0), 1.0)
    assert ftest(math.pow(-2.0, -1.0), -0.5)
    assert ftest(math.pow(-2.0, -2.0), 0.25)
    assert ftest(math.pow(-2.0, -3.0), -0.125)

    # the following tests have been commented out since they don't
    # really belong here:  the implementation of ** for floats is
    # independent of the implementation of math.pow
    #assert 1**NAN == 1
    #assert 1**INF == 1
    #assert 1**NINF == 1
    #assert 1**0 == 1
    #assert 1.**NAN == 1
    #assert 1.**INF == 1
    #assert 1.**NINF == 1
    #assert 1.**0 == 1

def testRadians():
    assert ftest(math.radians(180), math.pi)
    assert ftest(math.radians(90), math.pi/2)
    assert ftest(math.radians(-45), -math.pi/4)
    assert ftest(math.radians(0), 0)

# Too complicated for backends right now.
def testRemainder():
    """
    from fractions import Fraction

    def validate_spec(x, y, r):
        Check that r matches remainder(x, y) according to the IEEE 754
        specification. Assumes that x, y and r are finite and y is nonzero.
        fx, fy, fr = Fraction(x), Fraction(y), Fraction(r)
        # r should not exceed y/2 in absolute value
        assert abs(fr) <= abs(fy/2)
        # x - r should be an exact integer multiple of y
        n = (fx - fr) / fy
        assert n == int(n)
        if abs(fr) == abs(fy/2):
            # If |r| == |y/2|, n should be even.
            assert n/2 == int(n/2)

    # triples (x, y, remainder(x, y)) in hexadecimal form.
    testcases = [
        # Remainders modulo 1, showing the ties-to-even behaviour.
        '-4.0 1 -0.0',
        '-3.8 1  0.8',
        '-3.0 1 -0.0',
        '-2.8 1 -0.8',
        '-2.0 1 -0.0',
        '-1.8 1  0.8',
        '-1.0 1 -0.0',
        '-0.8 1 -0.8',
        '-0.0 1 -0.0',
        ' 0.0 1  0.0',
        ' 0.8 1  0.8',
        ' 1.0 1  0.0',
        ' 1.8 1 -0.8',
        ' 2.0 1  0.0',
        ' 2.8 1  0.8',
        ' 3.0 1  0.0',
        ' 3.8 1 -0.8',
        ' 4.0 1  0.0',

        # Reductions modulo 2*pi
        '0x0.0p+0 0x1.921fb54442d18p+2 0x0.0p+0',
        '0x1.921fb54442d18p+0 0x1.921fb54442d18p+2  0x1.921fb54442d18p+0',
        '0x1.921fb54442d17p+1 0x1.921fb54442d18p+2  0x1.921fb54442d17p+1',
        '0x1.921fb54442d18p+1 0x1.921fb54442d18p+2  0x1.921fb54442d18p+1',
        '0x1.921fb54442d19p+1 0x1.921fb54442d18p+2 -0x1.921fb54442d17p+1',
        '0x1.921fb54442d17p+2 0x1.921fb54442d18p+2 -0x0.0000000000001p+2',
        '0x1.921fb54442d18p+2 0x1.921fb54442d18p+2  0x0p0',
        '0x1.921fb54442d19p+2 0x1.921fb54442d18p+2  0x0.0000000000001p+2',
        '0x1.2d97c7f3321d1p+3 0x1.921fb54442d18p+2  0x1.921fb54442d14p+1',
        '0x1.2d97c7f3321d2p+3 0x1.921fb54442d18p+2 -0x1.921fb54442d18p+1',
        '0x1.2d97c7f3321d3p+3 0x1.921fb54442d18p+2 -0x1.921fb54442d14p+1',
        '0x1.921fb54442d17p+3 0x1.921fb54442d18p+2 -0x0.0000000000001p+3',
        '0x1.921fb54442d18p+3 0x1.921fb54442d18p+2  0x0p0',
        '0x1.921fb54442d19p+3 0x1.921fb54442d18p+2  0x0.0000000000001p+3',
        '0x1.f6a7a2955385dp+3 0x1.921fb54442d18p+2  0x1.921fb54442d14p+1',
        '0x1.f6a7a2955385ep+3 0x1.921fb54442d18p+2  0x1.921fb54442d18p+1',
        '0x1.f6a7a2955385fp+3 0x1.921fb54442d18p+2 -0x1.921fb54442d14p+1',
        '0x1.1475cc9eedf00p+5 0x1.921fb54442d18p+2  0x1.921fb54442d10p+1',
        '0x1.1475cc9eedf01p+5 0x1.921fb54442d18p+2 -0x1.921fb54442d10p+1',

        # Symmetry with respect to signs.
        ' 1  0.c  0.4',
        '-1  0.c -0.4',
        ' 1 -0.c  0.4',
        '-1 -0.c -0.4',
        ' 1.4  0.c -0.4',
        '-1.4  0.c  0.4',
        ' 1.4 -0.c -0.4',
        '-1.4 -0.c  0.4',

        # Huge modulus, to check that the underlying algorithm doesn't
        # rely on 2.0 * modulus being representable.
        '0x1.dp+1023 0x1.4p+1023  0x0.9p+1023',
        '0x1.ep+1023 0x1.4p+1023 -0x0.ap+1023',
        '0x1.fp+1023 0x1.4p+1023 -0x0.9p+1023',
    ]

    for case in testcases:
            x_hex, y_hex, expected_hex = case.split()
            x = float.fromhex(x_hex)
            y = float.fromhex(y_hex)
            expected = float.fromhex(expected_hex)
            validate_spec(x, y, expected)
            actual = math.remainder(x, y)
            # Cheap way of checking that the floats are
            # as identical as we need them to be.
            assert actual.hex() == expected.hex()

    # Test tiny subnormal modulus: there's potential for
    # getting the implementation wrong here (for example,
    # by assuming that modulus/2 is exactly representable).
    tiny = float.fromhex('1p-1074')  # min +ve subnormal
    for n in range(-25, 25):
        if n == 0:
            continue
        y = n * tiny
        for m in range(100):
            x = m * tiny
            actual = math.remainder(x, y)
            validate_spec(x, y, actual)
            actual = math.remainder(-x, y)
            validate_spec(-x, y, actual)

    # Special values.
    # NaNs should propagate as usual.
    for value in [NAN, 0.0, -0.0, 2.0, -2.3, NINF, INF]:
        assert math.isnan(math.remainder(NAN, value))
        assert math.isnan(math.remainder(value, NAN))

    # remainder(x, inf) is x, for non-nan non-infinite x.
    for value in [-2.3, -0.0, 0.0, 2.3]:
        assert math.remainder(value, INF) == value
        assert math.remainder(value, NINF) == value
    """


def testSin():
    assert ftest(math.sin(0), 0)
    assert ftest(math.sin(math.pi/2), 1)
    assert ftest(math.sin(-math.pi/2), -1)
    assert math.isnan(math.sin(NAN))

def testSinh():
    assert ftest(math.sinh(0), 0)
    assert ftest(math.sinh(1)**2-math.cosh(1)**2, -1)
    assert ftest(math.sinh(1)+math.sinh(-1), 0)
    assert math.sinh(INF) == INF
    assert math.sinh(NINF) == NINF
    assert math.isnan(math.sinh(NAN))

def testSqrt():
    assert ftest(math.sqrt(0), 0)
    assert ftest(math.sqrt(0.0), 0.0)
    assert ftest(math.sqrt(2.5), 1.5811388300841898)
    assert ftest(math.sqrt(0.25), 0.5)
    assert ftest(math.sqrt(25.25), 5.024937810560445)
    assert ftest(math.sqrt(1), 1)
    assert ftest(math.sqrt(4), 2)
    assert math.sqrt(INF) == INF
    assert math.isnan(math.sqrt(NAN))

def testTan():
    assert ftest(math.tan(0), 0)
    assert ftest(math.tan(math.pi/4), 1)
    assert ftest(math.tan(-math.pi/4), -1)
    assert math.isnan(math.tan(NAN))

def testTanh():
    assert ftest(math.tanh(0), 0)
    assert ftest(math.tanh(1)+math.tanh(-1), 0)
    assert ftest(math.tanh(INF), 1)
    assert ftest(math.tanh(NINF), -1)
    assert math.isnan(math.tanh(NAN))

def testTanhSign():
    # check that tanh(-0.) == -0. on IEEE 754 systems
    assert math.tanh(-0.) == -0.
    assert math.copysign(1., math.tanh(-0.)) == math.copysign(1., -0.)

def test_trunc():
    assert math.trunc(1) == 1
    assert math.trunc(-1) == -1
    assert math.trunc(1.5) == 1
    assert math.trunc(-1.5) == -1
    assert math.trunc(1.999999) == 1
    assert math.trunc(-1.999999) == -1
    assert math.trunc(-0.999999) == -0
    assert math.trunc(-100.999) == -100


def testIsfinite():
    assert math.isfinite(0.0)
    assert math.isfinite(-0.0)
    assert math.isfinite(1.0)
    assert math.isfinite(-1.0)
    assert not math.isfinite(float("nan"))
    assert not math.isfinite(float("inf"))
    assert not math.isfinite(float("-inf"))

def testIsnan():
    assert math.isnan(float("nan"))
    assert math.isnan(float("-nan"))
    assert math.isnan(float("inf") * 0.)
    assert not math.isnan(float("inf"))
    assert not math.isnan(0.)
    assert not math.isnan(1.)

def testIsinf():
    assert math.isinf(float("inf"))
    assert math.isinf(float("-inf"))
    assert math.isinf(1E400)
    assert math.isinf(-1E400)
    assert not math.isinf(float("nan"))
    assert not math.isinf(0.)
    assert not math.isinf(1.)

def test_nan_constant():
    assert math.isnan(math.nan)

def test_inf_constant():
    assert math.isinf(math.inf)
    assert math.inf > 0.0
    assert math.inf == float("inf")
    assert -math.inf == float("-inf")

def _naive_prod(iterable, start=1):
    for elem in iterable:
        start *= elem
    return start

def test_prod():
    assert prod([]) == 1
    assert prod([], start=5) == 5
    assert prod(list(range(2,8))) == 5040
    assert prod(iter(list(range(2,8)))) == 5040
    assert prod(range(1, 10), start=10) == 3628800

    assert prod([1, 2, 3, 4, 5]) == 120
    assert prod([1.0, 2.0, 3.0, 4.0, 5.0]) == 120.0
    assert prod([1, 2, 3, 4.0, 5.0]) == 120.0
    assert prod([1.0, 2.0, 3.0, 4, 5]) == 120.0

    # Test overflow in fast-path for integers
    assert prod([1, 1, 2**32, 1, 1]) == 2**32
    # Test overflow in fast-path for floats
    assert prod([1.0, 1.0, 2**32, 1, 1]) == float(2**32)

    values = [bytearray(b'a'), bytearray(b'b')]

    # Some odd cases
    assert prod([2, 3], start='ab') == 'abababababab'
    assert prod([2, 3], start=[1, 2]), [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1 == 2]
    assert prod([], start={2: 3}) == {2:3}

    assert prod([0, 1, 2, 3]) == 0
    assert prod([1, 0, 2, 3]) == 0
    assert prod([1, 2, 3, 0]) == 0

    # Big integers

    iterable = range(1, 10000)
    assert prod(iterable) == _naive_prod(iterable)
    iterable = range(-10000, -1)
    assert prod(iterable) == _naive_prod(iterable)
    iterable = range(-1000, 1000)
    assert prod(iterable) == 0

    # Big floats

    iterable = [float(x) for x in range(1, 1000)]
    assert prod(iterable) == _naive_prod(iterable)
    iterable = [float(x) for x in range(-1000, -1)]
    assert prod(iterable) == _naive_prod(iterable)
    iterable = [float(x) for x in range(-1000, 1000)]
    assert math.isnan(prod(iterable))

    # Float tests

    assert math.isnan(prod([1, 2, 3, float("nan"), 2, 3]))
    assert math.isnan(prod([1, 0, float("nan"), 2, 3]))
    assert math.isnan(prod([1, float("nan"), 0, 3]))
    assert math.isnan(prod([1, float("inf"), float("nan"),3]))
    assert math.isnan(prod([1, float("-inf"), float("nan"),3]))
    assert math.isnan(prod([1, float("nan"), float("inf"),3]))
    assert math.isnan(prod([1, float("nan"), float("-inf"),3]))

    assert prod([1, 2, 3, float('inf'),-3,4]) == float('-inf')
    assert prod([1, 2, 3, float('-inf'),-3,4]) == float('inf')

    assert math.isnan(prod([1,2,0,float('inf'), -3, 4]))
    assert math.isnan(prod([1,2,0,float('-inf'), -3, 4]))
    assert math.isnan(prod([1, 2, 3, float('inf'), -3, 0, 3]))
    assert math.isnan(prod([1, 2, 3, float('-inf'), -3, 0, 2]))

def testPerm():
    # Test if factorial definition is satisfied
    for n in range(500):
        for k in (range(n + 1) if n < 100 else range(30) if n < 200 else range(10)):
            assert math.perm(n, k) == math.factorial(n) // math.factorial(n - k)

    # Test for Pascal's identity
    for n in range(1, 100):
        for k in range(1, n):
            assert math.perm(n, k) == math.perm(n - 1, k - 1) * k + math.perm(n - 1, k)

    # Test corner cases
    for n in range(1, 100):
        assert math.perm(n, 0) == 1
        assert math.perm(n, 1) == n
        assert math.perm(n, n) == math.factorial(n)

    # Test one argument form
    for n in range(20):
        assert math.perm(n) == math.factorial(n)
        assert math.perm(n, None) == math.factorial(n)

    # Raises TypeError if any argument is non-integer or argument count is
    # not 1 or 2


    # Raises Value error if not k or n are negative numbers

    # Returns zero if k is greater than n
    assert math.perm(1, 2) == 0
    assert math.perm(1, 2**1000) == 0

    n = 2**1000
    assert math.perm(n, 0) == 1
    assert math.perm(n, 1) == n
    assert math.perm(n, 2) == n * (n-1)

    for n, k in (True, True), (True, False), (False, False):
        assert math.perm(n, k) == 1

def testComb():
    # Test if factorial definition is satisfied
    for n in range(500):
        for k in (range(n + 1) if n < 100 else range(30) if n < 200 else range(10)):
            assert math.comb(n, k) == math.factorial(n) // (math.factorial(k) * math.factorial(n - k))

    # Test for Pascal's identity
    for n in range(1, 100):
        for k in range(1, n):
            assert math.comb(n, k) == math.comb(n - 1, k - 1) + math.comb(n - 1, k)

    # Test corner cases
    for n in range(100):
        assert math.comb(n, 0) == 1
        assert math.comb(n, n) == 1

    for n in range(1, 100):
        assert math.comb(n, 1) == n
        assert math.comb(n, n - 1) == n

    # Test Symmetry
    for n in range(100):
        for k in range(n // 2):
            assert math.comb(n, k), math.comb(n == n - k)

    # Returns zero if k is greater than n
    assert math.comb(1, 2) == 0
    assert math.comb(1, 2**1000) == 0

    n = 2**1000
    assert math.comb(n, 0) == 1
    assert math.comb(n, 1) == n
    assert math.comb(n, 2) == n * (n-1) // 2
    assert math.comb(n, n) == 1
    assert math.comb(n, n-1) == n
    assert math.comb(n, n-2) == n * (n-1) // 2

    for n, k in (True, True), (True, False), (False, False):
        assert math.comb(n, k) == 1

def main():
    print("a")
    testConstants()
    testAcos()
    testAcosh()
    testAsin()
    testAsinh()
    testAtan()
    testAtanh()
    testAtan2()
    testCbrt()
    testCeil()
    testCopysign()
    testCos()
    testCosh()
    testDegrees()
    testExp()
    testExp2()
    testFabs()
    testFactorial()
    testFloor()
    testFmod()
    testFrexp()
    testFsum()
    testGcd()
    testHypot()
    testDist()
    testIsqrt()
    test_lcm()
    testLdexp()
    testLog()
    testLog1p()
    testLog2()
    testLog2Exact()
    testLog10()
    testModf()
    testPow()
    testRadians()
    testRemainder()
    testSin()
    testSinh()
    testSqrt()
    testTan()
    testTanh()
    testTanhSign()
    test_trunc()
    testIsfinite()
    testIsnan()
    testIsinf()
    test_nan_constant()
    test_inf_constant()
    test_prod()
    testPerm()
    testComb()

if __name__ == '__main__':
    main()