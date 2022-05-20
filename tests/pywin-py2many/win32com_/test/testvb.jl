using PyCall
pythoncom = pyimport("pythoncom")
import copy

import winerror
import win32com_.client
import win32com_.client.dynamic
import win32com_.client.gencache
using win32com_.server.util: NewCollection, wrap
using win32com_.test: util
using pywin32_testutil: str2memory

abstract type AbstractTestObject end
useDispatcher = nothing
error = RuntimeError
mutable struct TestObject <: AbstractTestObject
    _public_methods_::Vector{String}

    TestObject(
        _public_methods_::Vector{String} = [
            "CallbackVoidOneByRef",
            "CallbackResultOneByRef",
            "CallbackVoidTwoByRef",
            "CallbackString",
            "CallbackResultOneByRefButReturnNone",
            "CallbackVoidOneByRefButReturnNone",
            "CallbackArrayResult",
            "CallbackArrayResultOneArrayByRef",
            "CallbackArrayResultWrongSize",
        ],
    ) = new(_public_methods_)
end
function CallbackVoidOneByRef(self::TestObject, intVal)::Int64
    return intVal + 1
end

function CallbackResultOneByRef(self::TestObject, intVal)
    return (intVal, intVal + 1)
end

function CallbackVoidTwoByRef(self::TestObject, int1, int2)::Tuple
    return (int1 + int2, int1 - int2)
end

function CallbackString(self::TestObject, strVal)
    return (0, strVal + " has visited Python")
end

function CallbackArrayResult(self::TestObject, arrayVal)::Vector
    ret = []
    for i in arrayVal
        push!(ret, i + 1)
    end
    return ret
end

function CallbackArrayResultWrongSize(self::TestObject, arrayVal)::Vector
    return collect(arrayVal[begin:-1])
end

function CallbackArrayResultOneArrayByRef(self::TestObject, arrayVal)
    ret = []
    for i in arrayVal
        push!(ret, i + 1)
    end
    return (collect(arrayVal), ret)
end

function CallbackResultOneByRefButReturnNone(self::TestObject, intVal)
    return
end

function CallbackVoidOneByRefButReturnNone(self::TestObject, intVal)
    return
end

function TestVB(vbtest, bUseGenerated)
    vbtest.LongProperty = -1
    if vbtest.LongProperty != -1
        throw(error("Could not set the long property correctly."))
    end
    vbtest.IntProperty = 10
    if vbtest.IntProperty != 10
        throw(error("Could not set the integer property correctly."))
    end
    vbtest.VariantProperty = 10
    if vbtest.VariantProperty != 10
        throw(error("Could not set the variant integer property correctly."))
    end
    vbtest.VariantProperty = str2memory("raw\000data")
    if vbtest.VariantProperty != str2memory("raw\000data")
        throw(error("Could not set the variant buffer property correctly."))
    end
    vbtest.StringProperty = "Hello from Python"
    if vbtest.StringProperty != "Hello from Python"
        throw(error("Could not set the string property correctly."))
    end
    vbtest.VariantProperty = "Hello from Python"
    if vbtest.VariantProperty != "Hello from Python"
        throw(error("Could not set the variant string property correctly."))
    end
    vbtest.VariantProperty = (1.0, 2.0, 3.0)
    if vbtest.VariantProperty != (1.0, 2.0, 3.0)
        throw(
            error(
                "Could not set the variant property to an array of floats correctly - \'%s\'." %
                (vbtest.VariantProperty,),
            ),
        )
    end
    TestArrays(vbtest, bUseGenerated)
    TestStructs(vbtest)
    TestCollections(vbtest)
    @assert(TakeByValObject(vbtest, vbtest) === vbtest)
    if bUseGenerated
        ob = TakeByRefObject(vbtest, vbtest)
        @assert(ob[1] === vbtest && ob[2] === vbtest)
        vbtest.VariantPutref = vbtest
        if vbtest.VariantPutref._oleobj_ != vbtest._oleobj_
            throw(error("Could not set the VariantPutref property correctly."))
        end
        if IncrementIntegerParam(vbtest, 1) != 2
            throw(error("Could not pass an integer byref"))
        end
        if IncrementVariantParam(vbtest, 1) != 2
            throw(
                error(
                    "Could not pass an int VARIANT byref:" *
                    string(IncrementVariantParam(vbtest, 1)),
                ),
            )
        end
        if IncrementVariantParam(vbtest, 1.5) != 2.5
            throw(error("Could not pass a float VARIANT byref"))
        end
        callback_ob = wrap(TestObject(), useDispatcher)
        DoSomeCallbacks(vbtest, callback_ob)
    end
    ret = PassIntByVal(vbtest, 1)
    if ret != 2
        throw(error("Could not increment the integer - " * string(ret)))
    end
    TestVBInterface(vbtest)
    if bUseGenerated
        ret = PassIntByRef(vbtest, 1)
        if ret != (1, 2)
            throw(error("Could not increment the integer - " * string(ret)))
        end
    end
end

function _DoTestCollection(vbtest, col_name, expected)
    function _getcount(ob)
        r = getfield(ob, :Count)
        if type_(r) != type_(0)
            return r()
        end
        return r
    end

    c = getfield(vbtest, :col_name)
    check = []
    for item in c
        push!(check, item)
    end
    if check != collect(expected)
        throw(error("Collection %s didn\'t have %r (had %r)" % (col_name, expected, check)))
    end
    check = []
    for item in c
        push!(check, item)
    end
    if check != collect(expected)
        throw(
            error(
                "Collection 2nd time around %s didn\'t have %r (had %r)" %
                (col_name, expected, check),
            ),
        )
    end
    i = (x for x in getfield(vbtest, :col_name))
    check = []
    for item in i
        push!(check, item)
    end
    if check != collect(expected)
        throw(
            error(
                "Collection iterator %s didn\'t have %r 2nd time around (had %r)" %
                (col_name, expected, check),
            ),
        )
    end
    check = []
    for item in i
        push!(check, item)
    end
    if check != []
        throw(
            error(
                "2nd time around Collection iterator %s wasn\'t empty (had %r)" %
                (col_name, check),
            ),
        )
    end
    c = getfield(vbtest, :col_name)
    if length(c) != _getcount(c)
        throw(
            error(
                "Collection %s __len__(%r) wasn\'t==Count(%r)" %
                (col_name, length(c), _getcount(c)),
            ),
        )
    end
    c = getfield(vbtest, :col_name)
    check = []
    for i = 0:_getcount(c)-1
        push!(check, c[i+1])
    end
    if check != collect(expected)
        throw(error("Collection %s didn\'t have %r (had %r)" % (col_name, expected, check)))
    end
    c = _NewEnum(getfield(vbtest, :col_name))
    check = []
    while true
        n = Next(c)
        if !(n)
            has_break = true
            break
        end
        push!(check, n[1])
    end
    if check != collect(expected)
        throw(error("Collection %s didn\'t have %r (had %r)" % (col_name, expected, check)))
    end
end

function TestCollections(vbtest)
    _DoTestCollection(vbtest, "CollectionProperty", [1, "Two", "3"])
    if vbtest.CollectionProperty[1] != 1
        throw(error("The CollectionProperty[0] element was not the default value"))
    end
    _DoTestCollection(vbtest, "EnumerableCollectionProperty", [])
    Add(vbtest.EnumerableCollectionProperty, 1)
    Add(vbtest.EnumerableCollectionProperty, "Two")
    Add(vbtest.EnumerableCollectionProperty, "3")
    _DoTestCollection(vbtest, "EnumerableCollectionProperty", [1, "Two", "3"])
end

function _DoTestArray(vbtest, data, expected_exception = nothing)
    try
        vbtest.ArrayProperty = data
        if expected_exception != nothing
            throw(error("Expected \'%s\'" % expected_exception))
        end
    catch exn
        if exn isa expected_exception
            return
        end
    end
    got = vbtest.ArrayProperty
    if got != data
        throw(
            error(
                "Could not set the array data correctly - got %r, expected %r" %
                (got, data),
            ),
        )
    end
end

function TestArrays(vbtest, bUseGenerated)
    _DoTestArray(vbtest, ())
    _DoTestArray(vbtest, ((), ()))
    _DoTestArray(vbtest, tuple(1:99))
    _DoTestArray(vbtest, (1.0, 2.0, 3.0))
    _DoTestArray(vbtest, tuple(split("Hello from Python")))
    _DoTestArray(vbtest, (vbtest, vbtest))
    _DoTestArray(vbtest, (1, 2.0, "3"))
    _DoTestArray(vbtest, (1, (vbtest, vbtest), ("3", "4")))
    _DoTestArray(vbtest, ((1, 2, 3), (4, 5, 6)))
    _DoTestArray(vbtest, ((vbtest, vbtest, vbtest), (vbtest, vbtest, vbtest)))
    arrayData = (((1, 2), (3, 4), (5, 6)), ((7, 8), (9, 10), (11, 12)))
    arrayData = (
        ((vbtest, vbtest), (vbtest, vbtest), (vbtest, vbtest)),
        ((vbtest, vbtest), (vbtest, vbtest), (vbtest, vbtest)),
    )
    _DoTestArray(vbtest, arrayData)
    _DoTestArray(vbtest, (vbtest, 2.0, "3"))
    _DoTestArray(vbtest, (1, 2.0, vbtest))
    expected_exception = nothing
    arrayData = (((1, 2, 1), (3, 4), (5, 6)), ((7, 8), (9, 10), (11, 12)))
    _DoTestArray(vbtest, arrayData, expected_exception)
    arrayData = (((vbtest, vbtest),), ((vbtest,),))
    _DoTestArray(vbtest, arrayData, expected_exception)
    arrayData = (((1, 2), (3, 4), (5, 6, 8)), ((7, 8), (9, 10), (11, 12)))
    _DoTestArray(vbtest, arrayData, expected_exception)
    callback_ob = wrap(TestObject(), useDispatcher)
    println("** Expecting a \'ValueError\' exception to be printed next:")
    try
        DoCallbackSafeArraySizeFail(vbtest, callback_ob)
    catch exn
        let exc = exn
            if exc isa pythoncom.com_error
                @assert(exc.excepinfo[2] == "Python COM Server Internal Error")
            end
        end
    end
    if bUseGenerated
        testData = split("Mark was here")
        resultData, byRefParam = PassSAFEARRAY(vbtest, testData)
        if testData != collect(resultData)
            throw(
                error(
                    "The safe array data was not what we expected - got " *
                    string(resultData),
                ),
            )
        end
        if testData != collect(byRefParam)
            throw(
                error(
                    "The safe array data was not what we expected - got " *
                    string(byRefParam),
                ),
            )
        end
        testData = [1.0, 2.0, 3.0]
        resultData, byRefParam = PassSAFEARRAYVariant(vbtest, testData)
        @assert(testData == collect(byRefParam))
        @assert(testData == collect(resultData))
        testData = ["hi", "from", "Python"]
        resultData, byRefParam = PassSAFEARRAYVariant(vbtest, testData)
        @assert(testData == collect(byRefParam))
        @assert(testData == collect(resultData))
        testData = [1, 2.0, "3"]
        resultData, byRefParam = PassSAFEARRAYVariant(vbtest, testData)
        @assert(testData == collect(byRefParam))
        @assert(testData == collect(resultData))
    end
    println("Array tests passed")
end

function TestStructs(vbtest)
    try
        vbtest.IntProperty = "One"
        throw(error("Should have failed by now"))
    catch exn
        let exc = exn
            if exc isa pythoncom.com_error
                if exc.hresult != winerror.DISP_E_TYPEMISMATCH
                    throw(error("Expected DISP_E_TYPEMISMATCH"))
                end
            end
        end
    end
    s = vbtest.StructProperty
    if s.int_val != 99 || string(s.str_val) != "hello"
        throw(error("The struct value was not correct"))
    end
    s.str_val = "Hi from Python"
    s.int_val = 11
    if s.int_val != 11 || string(s.str_val) != "Hi from Python"
        throw(error("The struct value didnt persist!"))
    end
    if s.sub_val.int_val != 66 || string(s.sub_val.str_val) != "sub hello"
        throw(error("The sub-struct value was not correct"))
    end
    sub = s.sub_val
    sub.int_val = 22
    if sub.int_val != 22
        println(sub.int_val)
        throw(error("The sub-struct value didnt persist!"))
    end
    if s.sub_val.int_val != 22
        println(s.sub_val.int_val)
        throw(error("The sub-struct value (re-fetched) didnt persist!"))
    end
    if s.sub_val.array_val[1].int_val != 0 ||
       string(s.sub_val.array_val[1].str_val) != "zero"
        println(s.sub_val.array_val[1].int_val)
        throw(error("The array element wasnt correct"))
    end
    s.sub_val.array_val[1].int_val = 99
    s.sub_val.array_val[2].int_val = 66
    if s.sub_val.array_val[1].int_val != 99 || s.sub_val.array_val[2].int_val != 66
        println(s.sub_val.array_val[1].int_val)
        throw(error("The array element didnt persist."))
    end
    vbtest.StructProperty = s
    s = vbtest.StructProperty
    if s.int_val != 11 || string(s.str_val) != "Hi from Python"
        throw(error("After sending to VB, the struct value didnt persist!"))
    end
    if s.sub_val.array_val[1].int_val != 99
        throw(error("After sending to VB, the struct array value didnt persist!"))
    end
    @assert(s === s)
    @assert(s != nothing)
    if sys.version_info > (3, 0)
        try
            s < nothing
            throw(error("Expected type error"))
        catch exn
            if exn isa TypeError
                #= pass =#
            end
        end
        try
            nothing < s
            throw(error("Expected type error"))
        catch exn
            if exn isa TypeError
                #= pass =#
            end
        end
    end
    @assert(s != s.sub_val)
    s2 = copy(copy, s)
    @assert(s != s2)
    @assert(s === s2)
    s2.int_val = 123
    @assert(s != s2)
    s2 = GetStructFunc(vbtest)
    @assert(s === s2)
    SetStructSub(vbtest, s2)
    s = Record(win32com_.client, "VBStruct", vbtest)
    @assert(s.int_val == 0)
    s.int_val = -1
    SetStructSub(vbtest, s)
    @assert(GetStructFunc(vbtest).int_val == -1)
    s_array = vbtest.StructArrayProperty
    @assert(s_array === nothing)
    MakeStructArrayProperty(vbtest, 3)
    s_array = vbtest.StructArrayProperty
    @assert(length(s_array) == 3)
    for i = 0:length(s_array)-1
        @assert(s_array[i+1].int_val == i)
        @assert(s_array[i+1].sub_val.int_val == i)
        @assert(s_array[i+1].sub_val.array_val[1].int_val == i)
        @assert(s_array[i+1].sub_val.array_val[2].int_val == (i + 1))
        @assert(s_array[i+1].sub_val.array_val[3].int_val == (i + 2))
    end
    try
        s.bad_attribute
        throw(RuntimeError("Could get a bad attribute"))
    catch exn
        if exn isa AttributeError
            #= pass =#
        end
    end
    m = s.__members__
    @assert(m[1] == "int_val" && m[2] == "str_val" && m[3] == "ob_val" && m[4] == "sub_val")
    try
        s.foo
        throw(RuntimeError("Expected attribute error"))
    catch exn
        let exc = exn
            if exc isa AttributeError
                @assert(findfirst("foo", string(exc)) != Nothing)
            end
        end
    end
    expected =
        "com_struct(int_val=%r, str_val=%r, ob_val=%r, sub_val=%r)" %
        (s.int_val, s.str_val, s.ob_val, s.sub_val)
    if repr(s) != expected
        println("Expected repr:$(expected)")
        println("Actual repr  :$(repr(s))")
        throw(RuntimeError("repr() of record object failed"))
    end
    println("Struct/Record tests passed")
end

function TestVBInterface(ob)
    t = GetInterfaceTester(ob, 2)
    if getn(t) != 2
        throw(error("Initial value wrong"))
    end
    setn(t, 3)
    if getn(t) != 3
        throw(error("New value wrong"))
    end
end

function TestObjectSemantics(ob)
    @assert(ob == ob._oleobj_)
    @assert(!(ob != ob._oleobj_))
    @assert(ob._oleobj_ == ob)
    @assert(!(ob._oleobj_ != ob))
    @assert(ob._oleobj_ == QueryInterface(ob._oleobj_, pythoncom.IID_IUnknown))
    @assert(!(ob._oleobj_ != QueryInterface(ob._oleobj_, pythoncom.IID_IUnknown)))
    @assert(ob._oleobj_ != nothing)
    @assert(nothing != ob._oleobj_)
    @assert(ob != nothing)
    @assert(nothing != ob)
    if sys.version_info > (3, 0)
        try
            ob < nothing
            throw(error("Expected type error"))
        catch exn
            if exn isa TypeError
                #= pass =#
            end
        end
        try
            nothing < ob
            throw(error("Expected type error"))
        catch exn
            if exn isa TypeError
                #= pass =#
            end
        end
    end
    @assert(QueryInterface(ob._oleobj_, pythoncom.IID_IUnknown) == ob._oleobj_)
    @assert(!(QueryInterface(ob._oleobj_, pythoncom.IID_IUnknown) != ob._oleobj_))
    @assert(ob._oleobj_ == QueryInterface(ob._oleobj_, pythoncom.IID_IDispatch))
    @assert(!(ob._oleobj_ != QueryInterface(ob._oleobj_, pythoncom.IID_IDispatch)))
    @assert(QueryInterface(ob._oleobj_, pythoncom.IID_IDispatch) == ob._oleobj_)
    @assert(!(QueryInterface(ob._oleobj_, pythoncom.IID_IDispatch) != ob._oleobj_))
    println("Object semantic tests passed")
end

function DoTestAll()
    o = Dispatch(win32com_.client, "PyCOMVBTest.Tester")
    TestObjectSemantics(o)
    TestVB(o, 1)
    o = DumbDispatch(win32com_.client.dynamic, "PyCOMVBTest.Tester")
    TestObjectSemantics(o)
    TestVB(o, 0)
end

function TestAll()
    EnsureDispatch(win32com_.client.gencache, "PyCOMVBTest.Tester")
    if !(__debug__)
        throw(RuntimeError("This must be run in debug mode - we use assert!"))
    end
    try
        DoTestAll()
        println("All tests appear to have worked!")
    catch exn
        println("TestAll() failed!!")
        current_exceptions() != [] ? current_exceptions()[end] : nothing
        error()
    end
end

function suite()
    test = CapturingFunctionTestCase(util, TestAll, "VB tests")
    suite = TestSuite(unittest)
    addTest(suite, test)
    return suite
end

if abspath(PROGRAM_FILE) == @__FILE__
    testmain(util)
end
