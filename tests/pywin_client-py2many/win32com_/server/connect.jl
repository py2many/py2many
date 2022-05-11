module connect
#= Utilities for Server Side connections.

  A collection of helpers for server side connection points.
 =#
using Printf
using PyCall
pythoncom = pyimport("pythoncom")

using exception: Exception
import winerror
using win32com: olectl
import win32com.server.util
abstract type AbstractConnectableServer end
IConnectionPointContainer_methods = ["EnumConnectionPoints", "FindConnectionPoint"]
IConnectionPoint_methods = ["EnumConnections", "Unadvise", "Advise", "GetConnectionPointContainer", "GetConnectionInterface"]
mutable struct ConnectableServer <: AbstractConnectableServer
_connect_interfaces_::Any
_com_interfaces_::Vector
_public_methods_::Vector{String}
connections::Dict
cookieNo::Int64

                    ConnectableServer(_connect_interfaces_::Any, _com_interfaces_::Vector = [IID_IConnectionPoint(pythoncom), IID_IConnectionPointContainer(pythoncom)], _public_methods_::Vector{String} = append!(IConnectionPointContainer_methods, IConnectionPoint_methods), connections::Dict = Dict(), cookieNo::Int64 = 0) =
                        new(_connect_interfaces_, _com_interfaces_, _public_methods_, connections, cookieNo)
end
function EnumConnections(self::ConnectableServer)
throw(Exception(winerror.E_NOTIMPL))
end

function GetConnectionInterface(self::ConnectableServer)
throw(Exception(winerror.E_NOTIMPL))
end

function GetConnectionPointContainer(self::ConnectableServer)
return wrap(win32com.server.util, self)
end

function Advise(self::ConnectableServer, pUnk)::ConnectableServer
try
interface = QueryInterface(pUnk, self._connect_interfaces_[1], IID_IDispatch(pythoncom))
catch exn
if exn isa com_error(pythoncom)
throw(Exception(olectl.CONNECT_E_NOCONNECTION))
end
end
self.cookieNo = self.cookieNo + 1
self.connections[self.cookieNo + 1] = interface
return self.cookieNo
end

function Unadvise(self::ConnectableServer, cookie)
try
#Delete Unsupported
del(self.connections)
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
if iid in self._connect_interfaces_
return wrap(win32com.server.util, self)
end
end

function _BroadcastNotify(self::ConnectableServer, broadcaster, extraArgs)
for interface in values(self.connections)
try
broadcaster((interface,) + extraArgs...)
catch exn
 let details = exn
if details isa com_error(pythoncom)
_OnNotifyFail(self, interface, details)
end
end
end
end
end

function _OnNotifyFail(self::ConnectableServer, interface, details)
@printf("Ignoring COM error to connection - %s", repr(details))
end

end