module trybag
using PyCall
pythoncom = pyimport("pythoncom")

using win32com.server: util
using win32com.server: exception
abstract type AbstractBag end
abstract type AbstractTarget end
abstract type AbstractLog end
VT_EMPTY = VT_EMPTY(pythoncom)
mutable struct Bag <: AbstractBag
    _com_interfaces_::Vector
    _public_methods_::Vector{String}
    data::Dict

    Bag(
        _com_interfaces_::Vector = [IID_IPropertyBag(pythoncom)],
        _public_methods_::Vector{String} = ["Read", "Write"],
        data::Dict = Dict(),
    ) = new(_com_interfaces_, _public_methods_, data)
end
function Read(self::Bag, propName, varType, errorLog)
    println("read: name=", propName, "type=", varType)
    if propName
        not in self.data
        if errorLog
            hr = 2147942487
            exc = com_error(pythoncom, 0, "Bag.Read", "no such item", nothing, 0, hr)
            AddError(errorLog, propName, exc)
        end
        throw(Exception(exception, hr))
    end
    return self.data[propName+1]
end

function Write(self::Bag, propName, value)
    println("write: name=", propName, "value=", value)
    self.data[propName+1] = value
end

mutable struct Target <: AbstractTarget
    _com_interfaces_::Vector
    _public_methods_::Vector{String}

    Target(
        _com_interfaces_::Vector = [
            IID_IPersist(pythoncom),
            IID_IPersistPropertyBag(pythoncom),
        ],
        _public_methods_::Vector{String} = ["GetClassID", "InitNew", "Load", "Save"],
    ) = new(_com_interfaces_, _public_methods_)
end
function GetClassID(self::Target)
    throw(Exception(exception, 2147500037))
end

function InitNew(self::Target)
    #= pass =#
end

function Load(self::Target, bag, log)
    println(Read(bag, "prop1", VT_EMPTY, log))
    println(Read(bag, "prop2", VT_EMPTY, log))
    try
        println(Read(bag, "prop3", VT_EMPTY, log))
    catch exn
        if exn isa exception.Exception
            #= pass =#
        end
    end
end

function Save(self::Target, bag, clearDirty, saveAllProps)
    Write(bag, "prop1", "prop1.hello")
    Write(bag, "prop2", "prop2.there")
end

mutable struct Log <: AbstractLog
    _com_interfaces_::Vector
    _public_methods_::Vector{String}

    Log(
        _com_interfaces_::Vector = [IID_IErrorLog(pythoncom)],
        _public_methods_::Vector{String} = ["AddError"],
    ) = new(_com_interfaces_, _public_methods_)
end
function AddError(self::Log, propName, excepInfo)
    println("error: propName=", propName, "error=", excepInfo)
end

function test()
    bag = Bag()
    target = Target()
    log = Log()
    Save(target, bag, 1, 1)
    Load(target, bag, log)
    comBag = wrap(util, bag, IID_IPropertyBag(pythoncom))
    comTarget = wrap(util, target, IID_IPersistPropertyBag(pythoncom))
    comLog = wrap(util, log, IID_IErrorLog(pythoncom))
    Save(comTarget, comBag, 1, 1)
    Load(comTarget, comBag, comLog)
end

function main()
    test()
end

main()
end
