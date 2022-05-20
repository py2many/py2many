#= Utilities for Server Side connections.

  A collection of helpers for server side connection points.
 =#
using Printf
using PyCall
pythoncom = pyimport("pythoncom")

using exception: Exception
import winerror
using win32com_: olectl
import win32com_.server.util
abstract type AbstractConnectableServer end
IConnectionPointContainer_methods = ["EnumConnectionPoints", "FindConnectionPoint"]
IConnectionPoint_methods = [
    "EnumConnections",
    "Unadvise",
    "Advise",
    "GetConnectionPointContainer",
    "GetConnectionInterface",
]
mutable struct ConnectableServer <: AbstractConnectableServer
    _connect_interfaces_
    connections::Dict
    cookieNo::Int64
    _com_interfaces_::Vector
    _public_methods_::Vector{String}

    ConnectableServer(
        _connect_interfaces_,
        connections::Dict,
        cookieNo::Int64,
        _com_interfaces_::Vector = [
            pythoncom.IID_IConnectionPoint,
            pythoncom.IID_IConnectionPointContainer,
        ],
        _public_methods_::Vector{String} = append!(
            IConnectionPointContainer_methods,
            IConnectionPoint_methods,
        ),
    ) = new(_connect_interfaces_, connections, cookieNo, _com_interfaces_, _public_methods_)
end
function EnumConnections(self::ConnectableServer)
    throw(Exception(winerror.E_NOTIMPL))
end

function GetConnectionInterface(self::ConnectableServer)
    throw(Exception(winerror.E_NOTIMPL))
end

function GetConnectionPointContainer(self::ConnectableServer)
    return wrap(win32com_.server.util, self)
end

function Advise(self::ConnectableServer, pUnk)::Int64
    try
        interface =
            QueryInterface(pUnk, self._connect_interfaces_[1], pythoncom.IID_IDispatch)
    catch exn
        if exn isa pythoncom.com_error
            throw(Exception(olectl.CONNECT_E_NOCONNECTION))
        end
    end
    self.cookieNo = self.cookieNo + 1
    self.connections[self.cookieNo] = interface
    return self.cookieNo
end

function Unadvise(self::ConnectableServer, cookie)
    try
        delete!(self.connections, cookie)
    catch exn
        if exn isa KeyError
            throw(Exception(winerror.E_UNEXPECTED))
        end
    end
end

function EnumConnectionPoints(self::ConnectableServer)
    throw(Exception(winerror.E_NOTIMPL))
end

function FindConnectionPoint(self::ConnectableServer, iid)
    if iid ∈ self._connect_interfaces_
        return wrap(win32com_.server.util, self)
    end
end

function _BroadcastNotify(self::ConnectableServer, broadcaster, extraArgs)
    for interface in values(self.connections)
        try
            broadcaster((interface,) + extraArgs...)
        catch exn
            let details = exn
                if details isa pythoncom.com_error
                    _OnNotifyFail(self, interface, details)
                end
            end
        end
    end
end

function _OnNotifyFail(self::ConnectableServer, interface, details)
    @printf("Ignoring COM error to connection - %s\n", repr(details))
end
