using PyCall
pythoncom = pyimport("pythoncom")
import win32com_.server.util
import win32com_.server.policy
import win32com_.client.dynamic

import winerror
using win32com_.server.exception: Exception
abstract type AbstractVeryPermissive end
error = "testDynamic error"
iid = MakeIID(pythoncom, "{b48969a0-784b-11d0-ae71-d23f56000000}")
mutable struct VeryPermissive <: AbstractVeryPermissive
end
function _dynamic_(self::VeryPermissive, name, lcid, wFlags, args)
    if wFlags & pythoncom.DISPATCH_METHOD
        return getfield(self, :name)(args...)
    end
    if wFlags & pythoncom.DISPATCH_PROPERTYGET
        try
            ret = self.__dict__[name]
            if type_(ret) == type_(())
                ret = collect(ret)
            end
            return ret
        catch exn
            if exn isa KeyError
                throw(Exception(winerror.DISP_E_MEMBERNOTFOUND))
            end
        end
    end
    if wFlags & (pythoncom.DISPATCH_PROPERTYPUT | pythoncom.DISPATCH_PROPERTYPUTREF)
        setattr(self, name, args[1])
        return
    end
    throw(Exception(winerror.E_INVALIDARG, "invalid wFlags"))
end

function write(self::VeryPermissive)
    if length(args) == 0
        throw(Exception(winerror.DISP_E_BADPARAMCOUNT))
    end
    for arg in args[begin:-1]
        print("$(string(arg))")
    end
    println(string(args[end]))
end

function Test()
    ob =
        wrap(win32com_.server.util, VeryPermissive(), win32com_.server.policy.DynamicPolicy)
    try
        handle = RegisterActiveObject(pythoncom, ob, iid, 0)
    catch exn
        let details = exn
            if details isa pythoncom.com_error
                println("Warning - could not register the object in the ROT:$(details)")
                handle = nothing
            end
        end
    end
    try
        client = Dispatch(win32com_.client.dynamic, iid)
        client.ANewAttr = "Hello"
        if client.ANewAttr != "Hello"
            throw(error("Could not set dynamic property"))
        end
        v = ["Hello", "From", "Python", 1.4]
        client.TestSequence = v
        if v != collect(client.TestSequence)
            throw(
                error(
                    "Dynamic sequences not working! %r/%r" %
                    (repr(v), repr(client.testSequence)),
                ),
            )
        end
        write(client, "This", "output", "has", "come", "via", "testDynamic.py")
        _FlagAsMethod(client, "NotReallyAMethod")
        if !callable(client.NotReallyAMethod)
            throw(error("Method I flagged as callable isn\'t!"))
        end
        client = nothing
    finally
        if handle != nothing
            RevokeActiveObject(pythoncom, handle)
        end
    end
    println("Test worked!")
end

if abspath(PROGRAM_FILE) == @__FILE__
    Test()
end
