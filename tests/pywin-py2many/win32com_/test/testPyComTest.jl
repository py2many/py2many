using OrderedCollections
using PyCall
pythoncom = pyimport("pythoncom")
datetime = pyimport("datetime")
pywintypes = pyimport("pywintypes")
win32api = pyimport("win32api")
import win32com_.client.dynamic
using win32com_.client.gencache: EnsureDispatch
using win32com_.client.CLSIDToClass: GetClass
import random
import _thread

sys.coinit_flags = 0

import winerror
import win32com_
import win32com_.client.connect
using win32com_.test.util: CheckClean
using win32com_.client: constants, DispatchBaseClass, CastTo, VARIANT
using win32com_.test.util: RegisterPythonServer
using pywin32_testutil: str2memory

import decimal
import win32timezone
importMsg = "**** PyCOMTest is not installed ***\n  PyCOMTest is a Python test specific COM client and server.\n  It is likely this server is not installed on this machine\n  To install the server, you must get the win32com_ sources\n  and build it using MS Visual C++"
abstract type AbstractRandomEventHandler end
abstract type AbstractNewStyleRandomEventHandler <: Abstractobject end
abstract type AbstractTester <: Abstractwin32com_.test.util.TestCase end
error = Exception
RegisterPythonServer(join, "Python.Test.PyCOMTest")
using win32com_.client: gencache
try
    EnsureModule(gencache, "{6BCDCB60-5605-11D0-AE5F-CADD4C000000}", 0, 1, 1)
catch exn
    if exn isa pythoncom.com_error
        println("The PyCOMTest module can not be located or generated.")
        println(importMsg)
        throw(RuntimeError(importMsg))
    end
end
using win32com_: universal
RegisterInterfaces(universal, "{6BCDCB60-5605-11D0-AE5F-CADD4C000000}", 0, 1, 1)
verbose = 0
function check_get_set(func, arg)
    got = func(arg)
    if got != arg
        throw(error("%s failed - expected %r, got %r" % (func, arg, got)))
    end
end

function check_get_set_raises(exc, func, arg)
    try
        got = func(arg)
    catch exn
        let e = exn
            if e isa exc
                #= pass =#
            end
        end
    end
end

function progress()
    if verbose != 0
        for arg in args
            print("$(arg)")
        end
        println()
    end
end

function TestApplyResult(fn, args, result)
    try
        fnName = split(string(fn))[2]
    catch exn
        fnName = string(fn)
    end
    progress()
    pref = "function " + fnName
    rc = fn(args...)
    if rc != result
        throw(error("%s failed - result not %r but %r" % (pref, result, rc)))
    end
end

function TestConstant(constName, pyConst)
    try
        comConst = getfield(constants, :constName)
    catch exn
        throw(error("Constant %s missing" % (constName,)))
    end
    if comConst != pyConst
        throw(
            error(
                "Constant value wrong for %s - got %s, wanted %s" %
                (constName, comConst, pyConst),
            ),
        )
    end
end

mutable struct RandomEventHandler <: AbstractRandomEventHandler
    fireds::Dict
end
function _Init(self::RandomEventHandler)
    self.fireds = OrderedDict()
end

function OnFire(self::RandomEventHandler, no)
    try
        self.fireds[no] = self.fireds[no] + 1
    catch exn
        if exn isa KeyError
            self.fireds[no] = 0
        end
    end
end

function OnFireWithNamedParams(self::RandomEventHandler, no, a_bool, out1, out2)
    Missing = pythoncom.Missing
    if no != Missing
        @assert(no ∈ self.fireds)
        @assert((no + 1) == out1)
        @assert((no + 2) == out2)
    end
    @assert(a_bool == Missing || type_(a_bool) == bool)
    return (out1 + 2, out2 + 2)
end

function _DumpFireds(self::RandomEventHandler)
    if !(self.fireds)
        println("ERROR: Nothing was received!")
    end
    for (firedId, no) in items(self.fireds)
        progress()
    end
end

mutable struct NewStyleRandomEventHandler <: AbstractNewStyleRandomEventHandler
    fireds::Dict
end
function _Init(self::NewStyleRandomEventHandler)
    self.fireds = OrderedDict()
end

function OnFire(self::NewStyleRandomEventHandler, no)
    try
        self.fireds[no] = self.fireds[no] + 1
    catch exn
        if exn isa KeyError
            self.fireds[no] = 0
        end
    end
end

function OnFireWithNamedParams(self::NewStyleRandomEventHandler, no, a_bool, out1, out2)
    Missing = pythoncom.Missing
    if no != Missing
        @assert(no ∈ self.fireds)
        @assert((no + 1) == out1)
        @assert((no + 2) == out2)
    end
    @assert(a_bool == Missing || type_(a_bool) == bool)
    return (out1 + 2, out2 + 2)
end

function _DumpFireds(self::NewStyleRandomEventHandler)
    if !(self.fireds)
        println("ERROR: Nothing was received!")
    end
    for (firedId, no) in items(self.fireds)
        progress()
    end
end

function TestCommon(o, is_generated)
    progress()
    counter = GetSimpleCounter(o)
    TestCounter(counter, is_generated)
    progress()
    rc = TestOptionals(o)
    if rc[begin:-1] != ("def", 0, 1) || abs(rc[end] - 3.14) > 0.01
        println(rc)
        throw(error("Did not get the optional values correctly"))
    end
    rc = TestOptionals(o, "Hi", 2, 3, 1.1)
    if rc[begin:-1] != ("Hi", 2, 3) || abs(rc[end] - 1.1) > 0.01
        println(rc)
        throw(error("Did not get the specified optional values correctly"))
    end
    rc = TestOptionals2(o, 0)
    if rc != (0, "", 1)
        println(rc)
        throw(error("Did not get the optional2 values correctly"))
    end
    rc = TestOptionals2(o, 1.1, "Hi", 2)
    if rc[2:end] != ("Hi", 2) || abs(rc[1] - 1.1) > 0.01
        println(rc)
        throw(error("Did not get the specified optional2 values correctly"))
    end
    progress()
    check_get_set(o.GetSetUnknown, o)
    progress()
    expected_class = o.__class__
    expected_class = (
        hasfield(typeof(expected_class), :default_interface) ?
        getfield(expected_class, :default_interface) : expected_class
    )
    if !isa(GetSetDispatch(o, o), expected_class)
        throw(error("GetSetDispatch failed: %r" % (GetSetDispatch(o, o),)))
    end
    progress()
    expected_class = o.__class__
    expected_class = (
        hasfield(typeof(expected_class), :default_interface) ?
        getfield(expected_class, :default_interface) : expected_class
    )
    if GetSetInterface(o, o).__class__ != expected_class
        throw(error("GetSetDispatch failed"))
    end
    progress()
    check_get_set(o.GetSetVariant, 4)
    check_get_set(o.GetSetVariant, "foo")
    check_get_set(o.GetSetVariant, o)
    check_get_set(o.GetSetInt, 0)
    check_get_set(o.GetSetInt, -1)
    check_get_set(o.GetSetInt, 1)
    check_get_set(o.GetSetUnsignedInt, 0)
    check_get_set(o.GetSetUnsignedInt, 1)
    check_get_set(o.GetSetUnsignedInt, 2147483648)
    if GetSetUnsignedInt(o, -1) != 4294967295
        throw(error("unsigned -1 failed"))
    end
    check_get_set(o.GetSetLong, 0)
    check_get_set(o.GetSetLong, -1)
    check_get_set(o.GetSetLong, 1)
    check_get_set(o.GetSetUnsignedLong, 0)
    check_get_set(o.GetSetUnsignedLong, 1)
    check_get_set(o.GetSetUnsignedLong, 2147483648)
    if GetSetUnsignedLong(o, -1) != 4294967295
        throw(error("unsigned -1 failed"))
    end
    big = 2147483647
    for l in (big, big + 1, 1 << 65)
        check_get_set(o.GetSetVariant, l)
    end
    progress()
    r = GetStruct(o)
    @assert(r.int_value == 99 && string(r.str_value) == "Hello from C++")
    @assert(DoubleString(o, "foo") == "foofoo")
    progress()
    SetVarArgs(o, "Hi", "There", "From", "Python", 1)
    if GetLastVarArgs(o) != ("Hi", "There", "From", "Python", 1)
        throw(error("VarArgs failed -" * string(GetLastVarArgs(o))))
    end
    progress()
    l = []
    TestApplyResult(o.SetVariantSafeArray, (l,), length(l))
    l = [1, 2, 3, 4]
    TestApplyResult(o.SetVariantSafeArray, (l,), length(l))
    TestApplyResult(o.CheckVariantSafeArray, ((1, 2, 3, 4),), 1)
    TestApplyResult(o.SetBinSafeArray, (str2memory("foo\000bar"),), 7)
    progress()
    o.LongProp = 3
    if o.LongProp != 3 || o.IntProp != 3
        throw(error("Property value wrong - got %d/%d" % (o.LongProp, o.IntProp)))
    end
    o.LongProp = -3
    o.IntProp = -3
    if o.LongProp != -3 || o.IntProp != -3
        throw(error("Property value wrong - got %d/%d" % (o.LongProp, o.IntProp)))
    end
    check = 3 * 10^9
    o.ULongProp = check
    if o.ULongProp != check
        throw(error("Property value wrong - got %d (expected %d)" % (o.ULongProp, check)))
    end
    TestApplyResult(o.Test, ("Unused", 99), 1)
    TestApplyResult(o.Test, ("Unused", -1), 1)
    TestApplyResult(o.Test, ("Unused", 1 == 1), 1)
    TestApplyResult(o.Test, ("Unused", 0), 0)
    TestApplyResult(o.Test, ("Unused", 1 == 0), 0)
    @assert(DoubleString(o, "foo") == "foofoo")
    TestConstant("ULongTest1", 4294967295)
    TestConstant("ULongTest2", 2147483647)
    TestConstant("LongTest1", -2147483647)
    TestConstant("LongTest2", 2147483647)
    TestConstant("UCharTest", 255)
    TestConstant("CharTest", -1)
    TestConstant("StringTest", "Hello Wo®ld")
    progress()
    now = now(win32timezone)
    now = replace(now, 0)
    later = now + timedelta(datetime, 1)
    TestApplyResult(o.EarliestDate, (now, later), now)
    @assert(
        MakeDate(o, 18712.308206013888) ==
        fromisoformat(datetime.datetime, "1951-03-25 07:23:49+00:00")
    )
    progress()
    pythoncom.__future_currency__ = 1
    if o.CurrencyProp != 0
        throw(error("Expecting 0, got %r" % (o.CurrencyProp,)))
    end
    for val in ("1234.5678", "1234.56", "1234")
        o.CurrencyProp = Decimal(decimal, val)
        if o.CurrencyProp != Decimal(decimal, val)
            throw(error("%s got %r" % (val, o.CurrencyProp)))
        end
    end
    v1 = Decimal(decimal, "1234.5678")
    TestApplyResult(o.DoubleCurrency, (v1,), v1 * 2)
    v2 = Decimal(decimal, "9012.3456")
    TestApplyResult(o.AddCurrencies, (v1, v2), v1 + v2)
    TestTrickyTypesWithVariants(o, is_generated)
    progress()
    TestPyVariant(o, is_generated)
end

function TestTrickyTypesWithVariants(o, is_generated)
    if is_generated
        got = TestByRefVariant(o, 2)
    else
        v = VARIANT(pythoncom.VT_BYREF | pythoncom.VT_VARIANT, 2)
        TestByRefVariant(o, v)
        got = v.value
    end
    if got != 4
        throw(error("TestByRefVariant failed"))
    end
    if is_generated
        got = TestByRefString(o, "Foo")
    else
        v = VARIANT(pythoncom.VT_BYREF | pythoncom.VT_BSTR, "Foo")
        TestByRefString(o, v)
        got = v.value
    end
    if got != "FooFoo"
        throw(error("TestByRefString failed"))
    end
    vals = [1, 2, 3, 4]
    if is_generated
        arg = vals
    else
        arg = VARIANT(pythoncom.VT_ARRAY | pythoncom.VT_UI1, vals)
    end
    TestApplyResult(o.SetBinSafeArray, (arg,), length(vals))
    vals = [0, 1.1, 2.2, 3.3]
    if is_generated
        arg = vals
    else
        arg = VARIANT(pythoncom.VT_ARRAY | pythoncom.VT_R8, vals)
    end
    TestApplyResult(o.SetDoubleSafeArray, (arg,), length(vals))
    if is_generated
        arg = vals
    else
        arg = VARIANT(pythoncom.VT_ARRAY | pythoncom.VT_R4, vals)
    end
    TestApplyResult(o.SetFloatSafeArray, (arg,), length(vals))
    vals = [1.1, 2.2, 3.3, 4.4]
    expected = (1.1 * 2, 2.2 * 2, 3.3 * 2, 4.4 * 2)
    if is_generated
        TestApplyResult(o.ChangeDoubleSafeArray, (vals,), expected)
    else
        arg = VARIANT((pythoncom.VT_BYREF | pythoncom.VT_ARRAY) | pythoncom.VT_R8, vals)
        ChangeDoubleSafeArray(o, arg)
        if arg.value != expected
            throw(error("ChangeDoubleSafeArray got the wrong value"))
        end
    end
    if is_generated
        got = DoubleInOutString(o, "foo")
    else
        v = VARIANT(pythoncom.VT_BYREF | pythoncom.VT_BSTR, "foo")
        DoubleInOutString(o, v)
        got = v.value
    end
    @assert(got == "foofoo")
    val = Decimal(decimal, "1234.5678")
    if is_generated
        got = DoubleCurrencyByVal(o, val)
    else
        v = VARIANT(pythoncom.VT_BYREF | pythoncom.VT_CY, val)
        DoubleCurrencyByVal(o, v)
        got = v.value
    end
    @assert(got == (val * 2))
end

function TestDynamic()
    progress()
    o = DumbDispatch(win32com_.client.dynamic, "PyCOMTest.PyCOMTest")
    TestCommon(o, false)
    counter = DumbDispatch(win32com_.client.dynamic, "PyCOMTest.SimpleCounter")
    TestCounter(counter, false)
    try
        check_get_set_raises(ValueError, o.GetSetInt, "foo")
        throw(error("no exception raised"))
    catch exn
        let exc = exn
            if exc isa pythoncom.com_error
                if exc.hresult != winerror.DISP_E_TYPEMISMATCH
                    error()
                end
            end
        end
    end
    arg1 = VARIANT(pythoncom.VT_R4 | pythoncom.VT_BYREF, 2.0)
    arg2 = VARIANT(pythoncom.VT_BOOL | pythoncom.VT_BYREF, true)
    arg3 = VARIANT(pythoncom.VT_I4 | pythoncom.VT_BYREF, 4)
    TestInOut(o, arg1, arg2, arg3)
    @assert(arg1.value == 4.0)
    @assert(arg2.value == false)
    @assert(arg3.value == 8)
end

function TestGenerated()
    o = EnsureDispatch("PyCOMTest.PyCOMTest")
    TestCommon(o, true)
    counter = EnsureDispatch("PyCOMTest.SimpleCounter")
    TestCounter(counter, true)
    coclass_o = GetClass("{8EE0C520-5605-11D0-AE5F-CADD4C000000}")()
    TestCommon(coclass_o, true)
    @assert(Bool(coclass_o))
    coclass = GetClass("{B88DD310-BAE8-11D0-AE86-76F2C1000000}")()
    TestCounter(coclass, true)
    i1, i2 = GetMultipleInterfaces(o)
    if !isa(i1, DispatchBaseClass) || !isa(i2, DispatchBaseClass)
        throw(
            error(
                "GetMultipleInterfaces did not return instances - got \'%s\', \'%s\'" %
                (i1, i2),
            ),
        )
    end
    #Delete Unsupported
    del(i1)
    #Delete Unsupported
    del(i2)
    check_get_set_raises(OverflowError, o.GetSetInt, 2147483648)
    check_get_set_raises(OverflowError, o.GetSetLong, 2147483648)
    check_get_set_raises(ValueError, o.GetSetInt, "foo")
    check_get_set_raises(ValueError, o.GetSetLong, "foo")
    try
        SetVariantSafeArray(o, "foo")
        throw(error("Expected a type error"))
    catch exn
        if exn isa TypeError
            #= pass =#
        end
    end
    try
        SetVariantSafeArray(o, 666)
        throw(error("Expected a type error"))
    catch exn
        if exn isa TypeError
            #= pass =#
        end
    end
    GetSimpleSafeArray(o, nothing)
    TestApplyResult(o.GetSimpleSafeArray, (nothing,), tuple(0:9))
    resultCheck = (tuple(0:4), tuple(0:9), tuple(0:19))
    TestApplyResult(o.GetSafeArrays, (nothing, nothing, nothing), resultCheck)
    l = []
    TestApplyResult(o.SetIntSafeArray, (l,), length(l))
    l = [1, 2, 3, 4]
    TestApplyResult(o.SetIntSafeArray, (l,), length(l))
    ll = [1, 2, 3, 4294967296]
    TestApplyResult(o.SetLongLongSafeArray, (ll,), length(ll))
    TestApplyResult(o.SetULongLongSafeArray, (ll,), length(ll))
    TestApplyResult(o.Test2, (constants.Attr2,), constants.Attr2)
    TestApplyResult(o.Test3, (constants.Attr2,), constants.Attr2)
    TestApplyResult(o.Test4, (constants.Attr2,), constants.Attr2)
    TestApplyResult(o.Test5, (constants.Attr2,), constants.Attr2)
    TestApplyResult(o.Test6, (constants.WideAttr1,), constants.WideAttr1)
    TestApplyResult(o.Test6, (constants.WideAttr2,), constants.WideAttr2)
    TestApplyResult(o.Test6, (constants.WideAttr3,), constants.WideAttr3)
    TestApplyResult(o.Test6, (constants.WideAttr4,), constants.WideAttr4)
    TestApplyResult(o.Test6, (constants.WideAttr5,), constants.WideAttr5)
    TestApplyResult(o.TestInOut, (2.0, true, 4), (4.0, false, 8))
    SetParamProp(o, 0, 1)
    if ParamProp(o, 0) != 1
        throw(RuntimeError(paramProp(o, 0)))
    end
    o2 = CastTo(o, "IPyCOMTest")
    if o != o2
        throw(error("CastTo should have returned the same object"))
    end
    progress()
    o2 = DispatchWithEvents(win32com_.client, o, RandomEventHandler)
    TestEvents(o2, o2)
    o2 = DispatchWithEvents(win32com_.client, o, NewStyleRandomEventHandler)
    TestEvents(o2, o2)
    handler = WithEvents(win32com_.client, o, RandomEventHandler)
    TestEvents(o, handler)
    handler = WithEvents(win32com_.client, o, NewStyleRandomEventHandler)
    TestEvents(o, handler)
    progress()
end

function TestEvents(o, handler)
    sessions = []
    _Init(handler)
    try
        for i = 0:2
            session = Start(o)
            push!(sessions, session)
        end
        sleep(time, 0.5)
    finally
        for session in sessions
            Stop(o, session)
        end
        _DumpFireds(handler)
        close(handler)
    end
end

function _TestPyVariant(o, is_generated, val, checker = nothing)
    if is_generated
        vt, got = GetVariantAndType(o, val)
    else
        var_vt = VARIANT(pythoncom.VT_UI2 | pythoncom.VT_BYREF, 0)
        var_result = VARIANT(pythoncom.VT_VARIANT | pythoncom.VT_BYREF, 0)
        GetVariantAndType(o, val, var_vt, var_result)
        vt = var_vt.value
        got = var_result.value
    end
    if checker != nothing
        checker(got)
        return
    end
    @assert(vt == val.varianttype)
    if type_(val.value) ∈ (tuple, list)
        check = [isa(v, VARIANT) ? (v.value) : (v) for v in val.value]
        got = collect(got)
    else
        check = val.value
    end
    @assert(type_(check) == type_(got))
    @assert(check === got)
end

function _TestPyVariantFails(o, is_generated, val, exc)
    try
        _TestPyVariant(o, is_generated, val)
        throw(error("Setting %r didn\'t raise %s" % (val, exc)))
    catch exn
        if exn isa exc
            #= pass =#
        end
    end
end

function TestPyVariant(o, is_generated)
    _TestPyVariant(o, is_generated, VARIANT(pythoncom.VT_UI1, 1))
    _TestPyVariant(
        o,
        is_generated,
        VARIANT(pythoncom.VT_ARRAY | pythoncom.VT_UI4, [1, 2, 3]),
    )
    _TestPyVariant(o, is_generated, VARIANT(pythoncom.VT_BSTR, "hello"))
    _TestPyVariant(
        o,
        is_generated,
        VARIANT(pythoncom.VT_ARRAY | pythoncom.VT_BSTR, ["hello", "there"]),
    )
    function check_dispatch(got)
        @assert(isa(got._oleobj_, pythoncom.TypeIIDs[pythoncom.IID_IDispatch+1]))
    end

    _TestPyVariant(o, is_generated, VARIANT(pythoncom.VT_DISPATCH, o), check_dispatch)
    _TestPyVariant(
        o,
        is_generated,
        VARIANT(pythoncom.VT_ARRAY | pythoncom.VT_DISPATCH, [o]),
    )
    v = VARIANT(
        pythoncom.VT_ARRAY | pythoncom.VT_VARIANT,
        [
            VARIANT(pythoncom.VT_UI4, 1),
            VARIANT(pythoncom.VT_UI4, 2),
            VARIANT(pythoncom.VT_UI4, 3),
        ],
    )
    _TestPyVariant(o, is_generated, v)
    _TestPyVariantFails(o, is_generated, VARIANT(pythoncom.VT_UI1, "foo"), ValueError)
end

function TestCounter(counter, bIsGenerated)
    progress()
    for i = 0:49
        num = Int(pylib::random::random() * length(counter))
        try
            if bIsGenerated
                ret = Item(counter, num + 1)
            else
                ret = counter[num+1]
            end
            if ret != (num + 1)
                throw(
                    error(
                        "Random access into element %d failed - return was %s" %
                        (num, repr(ret)),
                    ),
                )
            end
        catch exn
            if exn isa IndexError
                throw(error("** IndexError accessing collection element %d" % num))
            end
        end
    end
    num = 0
    if bIsGenerated
        SetTestProperty(counter, 1)
        counter.TestProperty = 1
        SetTestProperty(counter, 1, 2)
        if counter.TestPropertyWithDef != 0
            throw(error("Unexpected property set value!"))
        end
        if TestPropertyNoDef(counter, 1) != 1
            throw(error("Unexpected property set value!"))
        end
    else
        #= pass =#
    end
    counter.LBound = 1
    counter.UBound = 10
    if counter.LBound != 1 || counter.UBound != 10
        println("** Error - counter did not keep its properties")
    end
    if bIsGenerated
        bounds = GetBounds(counter)
        if bounds[1] != 1 || bounds[2] != 10
            throw(error("** Error - counter did not give the same properties back"))
        end
        SetBounds(counter, bounds[1], bounds[2])
    end
    for item in counter
        num = num + 1
    end
    if num != length(counter)
        throw(error("*** Length of counter and loop iterations dont match ***"))
    end
    if num != 10
        throw(error("*** Unexpected number of loop iterations ***"))
    end
    try
        counter = Clone(None._iter_)
    catch exn
        if exn isa AttributeError
            progress()
            return
        end
    end
    Reset(counter)
    num = 0
    for item in counter
        num = num + 1
    end
    if num != 10
        throw(error("*** Unexpected number of loop iterations - got %d ***" % num))
    end
    progress()
end

function TestLocalVTable(ob)
    if DoubleString(ob, "foo") != "foofoo"
        throw(error("couldn\'t foofoo"))
    end
end

function TestVTable(clsctx = pythoncom.CLSCTX_ALL)
    ob = Dispatch(win32com_.client, "Python.Test.PyCOMTest")
    TestLocalVTable(ob)
    tester = Dispatch(win32com_.client, "PyCOMTest.PyCOMTest")
    testee = CoCreateInstance(
        pythoncom,
        "Python.Test.PyCOMTest",
        nothing,
        clsctx,
        pythoncom.IID_IUnknown,
    )
    try
        TestMyInterface(tester, nothing)
    catch exn
        let details = exn
            if details isa pythoncom.com_error
                #= pass =#
            end
        end
    end
    TestMyInterface(tester, testee)
end

function TestVTable2()
    ob = Dispatch(win32com_.client, "Python.Test.PyCOMTest")
    iid = pythoncom.InterfaceNames["IPyCOMTest"]
    clsid = "Python.Test.PyCOMTest"
    clsctx = pythoncom.CLSCTX_SERVER
    try
        testee = CoCreateInstance(pythoncom, clsid, nothing, clsctx, iid)
    catch exn
        if exn isa TypeError
            #= pass =#
        end
    end
end

function TestVTableMI()
    clsctx = pythoncom.CLSCTX_SERVER
    ob = CoCreateInstance(
        pythoncom,
        "Python.Test.PyCOMTestMI",
        nothing,
        clsctx,
        pythoncom.IID_IUnknown,
    )
    QueryInterface(ob, pythoncom.IID_IStream)
    QueryInterface(ob, pythoncom.IID_IStorage)
    QueryInterface(ob, pythoncom.IID_IDispatch)
    iid = pythoncom.InterfaceNames["IPyCOMTest"]
    try
        QueryInterface(ob, iid)
    catch exn
        if exn isa TypeError
            #= pass =#
        end
    end
end

function TestQueryInterface(long_lived_server = 0, iterations = 5)
    tester = Dispatch(win32com_.client, "PyCOMTest.PyCOMTest")
    if long_lived_server
        t0 = Dispatch(
            win32com_.client,
            "Python.Test.PyCOMTest",
            pythoncom.CLSCTX_LOCAL_SERVER,
        )
    end
    prompt = [
        "Testing QueryInterface without long-lived local-server #%d of %d...",
        "Testing QueryInterface with long-lived local-server #%d of %d...",
    ]
    for i = 0:iterations-1
        progress()
        TestQueryInterface(tester)
    end
end

mutable struct Tester <: AbstractTester
end
function testVTableInProc(self::Tester)
    for i = 0:2
        progress()
        TestVTable(pythoncom.CLSCTX_INPROC_SERVER)
    end
end

function testVTableLocalServer(self::Tester)
    for i = 0:2
        progress()
        TestVTable(pythoncom.CLSCTX_LOCAL_SERVER)
    end
end

function testVTable2(self::Tester)
    for i = 0:2
        TestVTable2()
    end
end

function testVTableMI(self::Tester)
    for i = 0:2
        TestVTableMI()
    end
end

function testMultiQueryInterface(self::Tester)
    TestQueryInterface(0, 6)
    TestQueryInterface(1, 6)
end

function testDynamic(self::Tester)
    TestDynamic()
end

function testGenerated(self::Tester)
    TestGenerated()
end

if abspath(PROGRAM_FILE) == @__FILE__
    function NullThreadFunc()
        #= pass =#
    end

    start_new(_thread, NullThreadFunc, ())
    if "-v" ∈ append!([PROGRAM_FILE], ARGS)
        verbose = 1
    end
    testmain(win32com_.test.util)
end
