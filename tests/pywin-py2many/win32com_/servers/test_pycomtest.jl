using PyCall
pythoncom = pyimport("pythoncom")
import win32com_.server.register
using win32com_: universal
using win32com_.server.exception: COMException
using win32com_.client: gencache
import winerror
using win32com_.client: constants
using win32com_.server.util: wrap

abstract type AbstractPyCOMTest end
abstract type AbstractPyCOMTestMI <: AbstractPyCOMTest end
pythoncom.__future_currency__ = true
EnsureModule(gencache, "{6BCDCB60-5605-11D0-AE5F-CADD4C000000}", 0, 1, 1)
mutable struct PyCOMTest <: AbstractPyCOMTest
    intval
    longval
    ulongval
    _com_interfaces_::Vector{String}
    _reg_clsid_::String
    _reg_progid_::String
    _typelib_guid_::String
    _typelib_version::Tuple{Int64}

    PyCOMTest(
        intval,
        longval,
        ulongval,
        _com_interfaces_::Vector{String} = ["IPyCOMTest"],
        _reg_clsid_::String = "{e743d9cd-cb03-4b04-b516-11d3a81c1597}",
        _reg_progid_::String = "Python.Test.PyCOMTest",
        _typelib_guid_::String = "{6BCDCB60-5605-11D0-AE5F-CADD4C000000}",
        _typelib_version::Tuple{Int64} = (1, 0),
    ) = new(
        intval,
        longval,
        ulongval,
        _com_interfaces_,
        _reg_clsid_,
        _reg_progid_,
        _typelib_guid_,
        _typelib_version,
    )
end
function DoubleString(self::PyCOMTest, str)::Int64
    return str * 2
end

function DoubleInOutString(self::PyCOMTest, str)::Int64
    return str * 2
end

function Fire(self::PyCOMTest, nID)
    throw(COMException(winerror.E_NOTIMPL))
end

function GetLastVarArgs(self::PyCOMTest)
    throw(COMException(winerror.E_NOTIMPL))
end

function GetMultipleInterfaces(self::PyCOMTest, outinterface1, outinterface2)
    throw(COMException(winerror.E_NOTIMPL))
end

function GetSafeArrays(self::PyCOMTest, attrs, attrs2, ints)
    throw(COMException(winerror.E_NOTIMPL))
end

function GetSetDispatch(self::PyCOMTest, indisp)
    throw(COMException(winerror.E_NOTIMPL))
end

function GetSetInterface(self::PyCOMTest, ininterface)
    return wrap(self)
end

function GetSetVariant(self::PyCOMTest, indisp)
    return indisp
end

function TestByRefVariant(self::PyCOMTest, v)::Int64
    return v * 2
end

function TestByRefString(self::PyCOMTest, v)::Int64
    return v * 2
end

function GetSetInterfaceArray(self::PyCOMTest, ininterface)
    throw(COMException(winerror.E_NOTIMPL))
end

function GetSetUnknown(self::PyCOMTest, inunk)
    throw(COMException(winerror.E_NOTIMPL))
end

function GetSimpleCounter(self::PyCOMTest)
    throw(COMException(winerror.E_NOTIMPL))
end

function GetSimpleSafeArray(self::PyCOMTest, ints)
    throw(COMException(winerror.E_NOTIMPL))
end

function GetStruct(self::PyCOMTest)
    throw(COMException(winerror.E_NOTIMPL))
end

function SetIntSafeArray(self::PyCOMTest, ints)::Int64
    return length(ints)
end

function SetLongLongSafeArray(self::PyCOMTest, ints)::Int64
    return length(ints)
end

function SetULongLongSafeArray(self::PyCOMTest, ints)::Int64
    return length(ints)
end

function SetBinSafeArray(self::PyCOMTest, buf)::Int64
    return length(buf)
end

function SetVarArgs(self::PyCOMTest)
    throw(COMException(winerror.E_NOTIMPL))
end

function SetVariantSafeArray(self::PyCOMTest, vars)
    throw(COMException(winerror.E_NOTIMPL))
end

function Start(self::PyCOMTest)
    throw(COMException(winerror.E_NOTIMPL))
end

function Stop(self::PyCOMTest, nID)
    throw(COMException(winerror.E_NOTIMPL))
end

function StopAll(self::PyCOMTest)
    throw(COMException(winerror.E_NOTIMPL))
end

function TakeByRefDispatch(self::PyCOMTest, inout)
    throw(COMException(winerror.E_NOTIMPL))
end

function TakeByRefTypedDispatch(self::PyCOMTest, inout)
    throw(COMException(winerror.E_NOTIMPL))
end

function Test(self::PyCOMTest, key, inval)
    return !(inval)
end

function Test2(self::PyCOMTest, inval)
    return inval
end

function Test3(self::PyCOMTest, inval)
    throw(COMException(winerror.E_NOTIMPL))
end

function Test4(self::PyCOMTest, inval)
    throw(COMException(winerror.E_NOTIMPL))
end

function Test5(self::PyCOMTest, inout)::Int64
    if inout == constants.TestAttr1
        return constants.TestAttr1_1
    elseif inout == constants.TestAttr1_1
        return constants.TestAttr1
    else
        return -1
    end
end

function Test6(self::PyCOMTest, inval)
    return inval
end

function TestInOut(self::PyCOMTest, fval, bval, lval)
    return (winerror.S_OK, fval * 2, !(bval), lval * 2)
end

function TestOptionals(
    self::PyCOMTest,
    strArg = "def",
    sval = 0,
    lval = 1,
    dval = 3.140000104904175,
)
    throw(COMException(winerror.E_NOTIMPL))
end

function TestOptionals2(self::PyCOMTest, dval, strval = "", sval = 1)
    throw(COMException(winerror.E_NOTIMPL))
end

function CheckVariantSafeArray(self::PyCOMTest, data)::Int64
    return 1
end

function LongProp(self::PyCOMTest)
    return self.longval
end

function SetLongProp(self::PyCOMTest, val)
    self.longval = val
end

function ULongProp(self::PyCOMTest)
    return self.ulongval
end

function SetULongProp(self::PyCOMTest, val)
    self.ulongval = val
end

function IntProp(self::PyCOMTest)
    return self.intval
end

function SetIntProp(self::PyCOMTest, val)
    self.intval = val
end

mutable struct PyCOMTestMI <: AbstractPyCOMTestMI
    _com_interfaces_::Vector{String}
    _reg_clsid_::String
    _reg_progid_::String
    _typelib_guid_::String
    _typelib_version::Tuple{Int64}

    PyCOMTestMI(
        _com_interfaces_::Vector{String} = [
            "IPyCOMTest",
            pythoncom.IID_IStream,
            string(pythoncom.IID_IStorage),
        ],
        _reg_clsid_::String = "{F506E9A1-FB46-4238-A597-FA4EB69787CA}",
        _reg_progid_::String = "Python.Test.PyCOMTestMI",
        _typelib_guid_::String = "{6BCDCB60-5605-11D0-AE5F-CADD4C000000}",
        _typelib_version::Tuple{Int64} = (1, 0),
    ) = new(_com_interfaces_, _reg_clsid_, _reg_progid_, _typelib_guid_, _typelib_version)
end

if abspath(PROGRAM_FILE) == @__FILE__
    UseCommandLine(win32com_.server.register, PyCOMTest)
    UseCommandLine(win32com_.server.register, PyCOMTestMI)
end
