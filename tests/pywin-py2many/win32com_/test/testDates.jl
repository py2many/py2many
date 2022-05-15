module testDates
using PyCall
pywintypes = pyimport("pywintypes")
datetime = pyimport("datetime")

import win32com_.client
import win32com_.test.util
import win32com_.server.util
using win32timezone: TimeZoneInfo
abstract type AbstractTester end
abstract type AbstractTestCase <: Abstractwin32com_.test.util.TestCase end
mutable struct Tester <: AbstractTester
    _public_methods_::Vector{String}

    Tester(_public_methods_::Vector{String} = ["TestDate"]) = new(_public_methods_)
end
function TestDate(self::Tester, d)
    @assert(isa(d, datetime))
    return d
end

function test_ob()
    return Dispatch(win32com_.client, wrap(win32com_.server.util, Tester()))
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
    check(
        self,
        datetime(
            year = 2000,
            month = 12,
            day = 25,
            microsecond = 500000,
            tzinfo = utc(TimeZoneInfo),
        ),
    )
end

function testLocal(self::TestCase)
    check(
        self,
        datetime(
            year = 2000,
            month = 12,
            day = 25,
            microsecond = 500000,
            tzinfo = local_(TimeZoneInfo),
        ),
    )
end

function testMSTruncated(self::TestCase)
    check(
        self,
        datetime(
            year = 2000,
            month = 12,
            day = 25,
            microsecond = 500500,
            tzinfo = utc(TimeZoneInfo),
        ),
        datetime(
            year = 2000,
            month = 12,
            day = 25,
            microsecond = 500000,
            tzinfo = utc(TimeZoneInfo),
        ),
    )
end

function main()
end

main()
end
