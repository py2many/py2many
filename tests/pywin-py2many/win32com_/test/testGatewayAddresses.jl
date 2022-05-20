using Printf
using PyCall
pythoncom = pyimport("pythoncom")
using win32com_.server.util: wrap

import CheckClean
abstract type AbstractDummy end
abstract type AbstractDummy2 end
abstract type AbstractDeletgatedDummy end
abstract type AbstractDummy3 end
numErrors = 0
function CheckSameCOMObject(ob1, ob2)::Bool
    addr1 = split(repr(ob1))[7][begin:-1]
    addr2 = split(repr(ob2))[7][begin:-1]
    return addr1 == addr2
end

function CheckObjectIdentity(ob1, ob2)::Bool
    u1 = QueryInterface(ob1, pythoncom.IID_IUnknown)
    u2 = QueryInterface(ob2, pythoncom.IID_IUnknown)
    return CheckSameCOMObject(u1, u2)
end

function FailObjectIdentity(ob1, ob2, when)
    if !CheckObjectIdentity(ob1, ob2)
        global numErrors
        numErrors = numErrors + 1
        @printf("are not identical (%s, %s)\n", repr(ob1), repr(ob2))
    end
end

mutable struct Dummy <: AbstractDummy
    _com_interfaces_::Vector
    _public_methods_::Vector

    Dummy(
        _com_interfaces_::Vector = [pythoncom.IID_IPersistStorage],
        _public_methods_::Vector = [],
    ) = new(_com_interfaces_, _public_methods_)
end

mutable struct Dummy2 <: AbstractDummy2
    _com_interfaces_::Vector
    _public_methods_::Vector

    Dummy2(
        _com_interfaces_::Vector = [
            pythoncom.IID_IPersistStorage,
            pythoncom.IID_IExternalConnection,
        ],
        _public_methods_::Vector = [],
    ) = new(_com_interfaces_, _public_methods_)
end

mutable struct DeletgatedDummy <: AbstractDeletgatedDummy
    _public_methods_::Vector

    DeletgatedDummy(_public_methods_::Vector = []) = new(_public_methods_)
end

mutable struct Dummy3 <: AbstractDummy3
    _com_interfaces_::Vector
    _public_methods_::Vector

    Dummy3(
        _com_interfaces_::Vector = [pythoncom.IID_IPersistStorage],
        _public_methods_::Vector = [],
    ) = new(_com_interfaces_, _public_methods_)
end
function _query_interface_(self::Dummy3, iid)
    if iid == pythoncom.IID_IExternalConnection
        return wrap(DelegatedDummy())
    end
end

function TestGatewayInheritance()
    o = wrap(Dummy(), pythoncom.IID_IPersistStorage)
    o2 = QueryInterface(o, pythoncom.IID_IUnknown)
    FailObjectIdentity(o, o2, "IID_IPersistStorage->IID_IUnknown")
    o3 = QueryInterface(o2, pythoncom.IID_IDispatch)
    FailObjectIdentity(o2, o3, "IID_IUnknown->IID_IDispatch")
    FailObjectIdentity(o, o3, "IID_IPersistStorage->IID_IDispatch")
    o4 = QueryInterface(o3, pythoncom.IID_IPersistStorage)
    FailObjectIdentity(o, o4, "IID_IPersistStorage->IID_IPersistStorage(2)")
    FailObjectIdentity(o2, o4, "IID_IUnknown->IID_IPersistStorage(2)")
    FailObjectIdentity(o3, o4, "IID_IDispatch->IID_IPersistStorage(2)")
    o5 = QueryInterface(o4, pythoncom.IID_IPersist)
    FailObjectIdentity(o, o5, "IID_IPersistStorage->IID_IPersist")
    FailObjectIdentity(o2, o5, "IID_IUnknown->IID_IPersist")
    FailObjectIdentity(o3, o5, "IID_IDispatch->IID_IPersist")
    FailObjectIdentity(o4, o5, "IID_IPersistStorage(2)->IID_IPersist")
end

function TestMultiInterface()
    o = wrap(Dummy2(), pythoncom.IID_IPersistStorage)
    o2 = QueryInterface(o, pythoncom.IID_IExternalConnection)
    FailObjectIdentity(o, o2, "IID_IPersistStorage->IID_IExternalConnection")
    o22 = QueryInterface(o, pythoncom.IID_IExternalConnection)
    FailObjectIdentity(o, o22, "IID_IPersistStorage->IID_IExternalConnection")
    FailObjectIdentity(o2, o22, "IID_IPersistStorage->IID_IExternalConnection (stability)")
    o3 = QueryInterface(o2, pythoncom.IID_IPersistStorage)
    FailObjectIdentity(o2, o3, "IID_IExternalConnection->IID_IPersistStorage")
    FailObjectIdentity(
        o,
        o3,
        "IID_IPersistStorage->IID_IExternalConnection->IID_IPersistStorage",
    )
end

function test()
    TestGatewayInheritance()
    TestMultiInterface()
    if numErrors == 0
        println("Worked ok")
    else
        println("There were$(numErrors)errors.")
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    test()
    CheckClean()
end
