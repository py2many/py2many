using PyCall
win32ui = pyimport("win32ui")


abstract type AbstractObject end
abstract type AbstractCmdTarget <: AbstractObject end
mutable struct Object <: AbstractObject
__dict__
_obj_
initObj

            Object(initObj = nothing) = begin
                if initObj != nothing
initObj.AttachObject(self)
end
                new(initObj )
            end
end
function __del__(self::Object)
close(self)
end

function __getattr__(self::Object, attr)
if !startswith(attr, "__")
try
o = self.__dict__["_obj_"]
if o != nothing
return getfield(o, :attr)
end
if attr[1] != "_" && attr[end] != "_"
throw(error(win32ui, "The MFC object has died."))
end
catch exn
if exn isa KeyError
#= pass =#
end
end
end
throw(AttributeError(attr))
end

function OnAttachedObjectDeath(self::Object)
self._obj_ = nothing
end

function close(self::Object)
if "_obj_" ∈ self.__dict__
if self._obj_ != nothing
AttachObject(self._obj_, nothing)
self._obj_ = nothing
end
end
end

mutable struct CmdTarget <: AbstractCmdTarget


            CmdTarget(initObj) = begin
                Object(initObj)
                new(initObj)
            end
end
function HookNotifyRange(self::CmdTarget, handler, firstID, lastID)::Vector
oldhandlers = []
for i in firstID:lastID
push!(oldhandlers, HookNotify(self, handler, i))
end
return oldhandlers
end

function HookCommandRange(self::CmdTarget, handler, firstID, lastID)::Vector
oldhandlers = []
for i in firstID:lastID
push!(oldhandlers, HookCommand(self, handler, i))
end
return oldhandlers
end

function HookCommandUpdateRange(self::CmdTarget, handler, firstID, lastID)::Vector
oldhandlers = []
for i in firstID:lastID
push!(oldhandlers, HookCommandUpdate(self, handler, i))
end
return oldhandlers
end
