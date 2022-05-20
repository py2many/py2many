
import win32com_.client
import win32com_.test.util
import win32com_.server.util
abstract type AbstractTester end
abstract type AbstractTestException <: AbstractException end
abstract type AbstractBadConversions end
abstract type AbstractTestCase <: Abstractwin32com_.test.util.TestCase end
mutable struct Tester <: AbstractTester
    _public_methods_::Vector{String}

    Tester(_public_methods_::Vector{String} = ["TestValue"]) = new(_public_methods_)
end
function TestValue(self::Tester, v)
    #= pass =#
end

function test_ob()
    return Dispatch(win32com_.client, wrap(win32com_.server.util, Tester()))
end

mutable struct TestException <: AbstractTestException
end

mutable struct BadConversions <: AbstractBadConversions
end
function __float__(self::BadConversions)
    throw(TestException())
end

mutable struct TestCase <: AbstractTestCase
end
function test_float(self::TestCase)
    try
        TestValue(test_ob(), BadConversions())
        throw(Exception("Should not have worked"))
    catch exn
        let e = exn
            if e isa Exception
                @assert(isa(e, TestException))
            end
        end
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
end
