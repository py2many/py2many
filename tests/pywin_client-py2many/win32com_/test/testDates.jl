module testDates
using PyCall
pywintypes = pyimport("pywintypes")
datetime = pyimport("datetime")



import win32com.client
import win32com.test.util
import win32com.server.util
using win32timezone: TimeZoneInfo
abstract type AbstractTester end
abstract type AbstractTestCase <: Abstractwin32com.test.util.TestCase end
mutable struct Tester <: AbstractTester
    _public_methods_::Vector{String}

    Tester(_public_methods_::Vector{String} = ["TestDate"]) = new(_public_methods_)
end
function TestDate(self::Tester, d)
    @assert(isa(d, datetime))
    return d
end

function test_ob()
    return Dispatch(win32com.client, wrap(win32com.server.util, Tester()))
end

mutable struct TestCase <: AbstractTestCase

end
function check(self::TestCase, d, expected = nothing)
    if !pywintypes.TimeType <: datetime
        skipTest(self, "this is testing pywintypes and datetime")
    end
    got = TestDate(test_ob(), d)
    assertEqual(self, got, expected || d)
end

function testUTC(self::TestCase)
    check(self, datetime(2000, 12, 25, 500000, utc(TimeZoneInfo)))
end

function testLocal(self::TestCase)
    check(self, datetime(2000, 12, 25, 500000, local_(TimeZoneInfo)))
end

function testMSTruncated(self::TestCase)
    check(
        self,
        datetime(2000, 12, 25, 500500, utc(TimeZoneInfo)),
        datetime(2000, 12, 25, 500000, utc(TimeZoneInfo)),
    )
end

function main()

end

main()
end
