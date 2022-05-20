#= Utilities for working with Connections =#
using PyCall
pythoncom = pyimport("pythoncom")
using win32com_.server: dispatcher

import win32com_.server.util
abstract type AbstractSimpleConnection end
mutable struct SimpleConnection <: AbstractSimpleConnection
    #= A simple, single connection object =#
    cookie
    cp
    debug
    coInstance
    eventCLSID
    eventInstance

    SimpleConnection(
        coInstance = nothing,
        eventInstance = nothing,
        eventCLSID = nothing,
        debug = 0,
    ) = begin
        if !(coInstance === nothing)
            Connect(coInstance, eventInstance, eventCLSID)
        end
        new(coInstance, eventInstance, eventCLSID, debug)
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
