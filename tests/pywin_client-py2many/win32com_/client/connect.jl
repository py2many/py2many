module connect
#= Utilities for working with Connections =#
using PyCall
pythoncom = pyimport("pythoncom")
using win32com.server: dispatcher

include("win32com_/server/util.jl")
abstract type AbstractSimpleConnection end
mutable struct SimpleConnection <: AbstractSimpleConnection
    #= A simple, single connection object =#
    debug::Any
    coInstance::Any
    cookie::Any
    cp::Any
    eventCLSID::Any
    eventInstance::Any

    SimpleConnection(
        coInstance = nothing,
        eventInstance = nothing,
        eventCLSID = nothing,
        debug = 0,
        cookie = nothing,
        cp = nothing,
    ) = begin
        if !(coInstance === nothing)
            self.Connect(coInstance, eventInstance, eventCLSID)
        end
        new(coInstance, eventInstance, eventCLSID, debug, cookie, cp)
    end
end
function __del__(self::SimpleConnection)
    try
        Disconnect(self)
    catch exn
        if exn isa pythoncom.error
            #= pass =#
        end
    end
end

function _wrap(self::SimpleConnection, obj)
    useDispatcher = nothing
    if self.debug
        useDispatcher = dispatcher.DefaultDebugDispatcher
    end
    return wrap(win32com_.server.util, obj, useDispatcher)
end

function Connect(self::SimpleConnection, coInstance, eventInstance, eventCLSID = nothing)
    try
        oleobj = coInstance._oleobj_
    catch exn
        if exn isa AttributeError
            oleobj = coInstance
        end
    end
    cpc = QueryInterface(oleobj, pythoncom.IID_IConnectionPointContainer)
    if eventCLSID === nothing
        eventCLSID = eventInstance.CLSID
    end
    comEventInstance = _wrap(self, eventInstance)
    self.cp = FindConnectionPoint(cpc, eventCLSID)
    self.cookie = Advise(self.cp, comEventInstance)
end

function Disconnect(self::SimpleConnection)
    if !(self.cp === nothing)
        if self.cookie
            Unadvise(self.cp, self.cookie)
            self.cookie = nothing
        end
        self.cp = nothing
    end
end

end
