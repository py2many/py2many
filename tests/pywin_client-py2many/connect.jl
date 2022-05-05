#= Utilities for working with Connections =#
abstract type AbstractSimpleConnection end
import win32com.server.util
import win32com.server.util
import win32com.server.util
import pythoncom
mutable struct SimpleConnection <: AbstractSimpleConnection
    cookie::Any
    cp::Any
    debug::Any
    coInstance::Any
    eventCLSID::Any
    eventInstance::Any

    SimpleConnection(
        coInstance = nothing,
        eventInstance = nothing,
        eventCLSID = nothing,
        debug = 0,
    ) = begin
        if !(coInstance === nothing)
            self.Connect(coInstance, eventInstance, eventCLSID)
        end
        new(coInstance = nothing, eventInstance = nothing, eventCLSID = nothing, debug = 0)
    end
end
function __del__(self::AbstractSimpleConnection)
    try
        Disconnect(self)
    catch exn
        if exn isa pythoncom.error
            #= pass =#
        end
    end
end

function _wrap(self::AbstractSimpleConnection, obj)
    useDispatcher = nothing
    if self.debug
        using win32com.server: dispatcher
        useDispatcher = DefaultDebugDispatcher(dispatcher)
    end
    return wrap(win32com.server.util, obj, useDispatcher)
end

function Connect(
    self::AbstractSimpleConnection,
    coInstance,
    eventInstance,
    eventCLSID = nothing,
)
    try
        oleobj = _oleobj_(coInstance)
    catch exn
        if exn isa AttributeError
            oleobj = coInstance
        end
    end
    cpc = QueryInterface(oleobj, pythoncom.IID_IConnectionPointContainer)
    if eventCLSID === nothing
        eventCLSID = CLSID(eventInstance)
    end
    comEventInstance = _wrap(self, eventInstance)
    self.cp = FindConnectionPoint(cpc, eventCLSID)
    self.cookie = Advise(self.cp, comEventInstance)
end

function Disconnect(self::AbstractSimpleConnection)
    if !(self.cp === nothing)
        if self.cookie
            Unadvise(self.cp, self.cookie)
            self.cookie = nothing
        end
        self.cp = nothing
    end
end
