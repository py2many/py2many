using win32com_.client: gencache
using win32com_.test: util

abstract type AbstractArrayTest <: Abstractutil.TestCase end
ZeroD = 0
OneDEmpty = []
OneD = [1, 2, 3]
TwoD = [[1, 2, 3], [1, 2, 3], [1, 2, 3]]
TwoD1 = [[[1, 2, 3, 5], [1, 2, 3], [1, 2, 3]], [[1, 2, 3], [1, 2, 3], [1, 2, 3]]]
OneD1 = [[[1, 2, 3], [1, 2, 3], [1, 2, 3]], [[1, 2, 3], [1, 2, 3]]]
OneD2 = [[1, 2, 3], [1, 2, 3, 4, 5], [[1, 2, 3, 4, 5], [1, 2, 3, 4, 5], [1, 2, 3, 4, 5]]]
ThreeD = [[[1, 2, 3], [1, 2, 3], [1, 2, 3]], [[1, 2, 3], [1, 2, 3], [1, 2, 3]]]
FourD = [
    [
        [[1, 2, 3], [1, 2, 3], [1, 2, 3]],
        [[1, 2, 3], [1, 2, 3], [1, 2, 3]],
        [[1, 2, 3], [1, 2, 3], [1, 2, 3]],
    ],
    [
        [[1, 2, 3], [1, 2, 3], [1, 2, 3]],
        [[1, 2, 3], [1, 2, 3], [1, 2, 3]],
        [[1, 2, 3], [1, 2, 3], [1, 2, 3]],
    ],
]
LargeD = repeat([[repeat([collect(0:9)], 10)]], 512)
function _normalize_array(a)::Vector
    if type_(a) != type_(())
        return a
    end
    ret = []
    for i in a
        push!(ret, _normalize_array(i))
    end
    return ret
end

mutable struct ArrayTest <: AbstractArrayTest
    arr
end
function setUp(self::ArrayTest)
    self.arr = EnsureDispatch(gencache, "PyCOMTest.ArrayTest")
end

function tearDown(self::ArrayTest)
    self.arr = nothing
end

function _doTest(self::ArrayTest, array)
    self.arr.Array = array
    assertEqual(self, _normalize_array(self.arr.Array), array)
end

function testZeroD(self::ArrayTest)
    _doTest(self, ZeroD)
end

function testOneDEmpty(self::ArrayTest)
    _doTest(self, OneDEmpty)
end

function testOneD(self::ArrayTest)
    _doTest(self, OneD)
end

function testTwoD(self::ArrayTest)
    _doTest(self, TwoD)
end

function testThreeD(self::ArrayTest)
    _doTest(self, ThreeD)
end

function testFourD(self::ArrayTest)
    _doTest(self, FourD)
end

function testTwoD1(self::ArrayTest)
    _doTest(self, TwoD1)
end

function testOneD1(self::ArrayTest)
    _doTest(self, OneD1)
end

function testOneD2(self::ArrayTest)
    _doTest(self, OneD2)
end

function testLargeD(self::ArrayTest)
    _doTest(self, LargeD)
end

if abspath(PROGRAM_FILE) == @__FILE__
    try
        testmain(util)
    catch exn
        let rc = exn
            if rc isa SystemExit
                if !(rc)
                    error()
                end
            end
        end
    end
end
