#= Support for ActiveX control hosting in Pythonwin.
 =#
using PyCall
win32ui = pyimport("win32ui")
import win32uiole
include("window.jl")
try

catch exn
if exn isa ImportError
new_type = type_
end
end
abstract type AbstractControl <: Abstractwindow.Wnd end
mutable struct Control <: AbstractControl
#= An ActiveX control base class.  A new class must be derived from both
    this class and the Events class.  See the demos for more details.
     =#
CLSID
default_interface
default_source
_dispobj_
__dict__

            Control() = begin
                window.Wnd.__init__(self)
                new()
            end
end
function _GetControlCLSID(self::Control)
return self.CLSID
end

function _GetDispatchClass(self::Control)
return self.default_interface
end

function _GetEventMap(self::Control)
return self.default_source._dispid_to_func_
end

function CreateControl(self::Control, windowTitle, style, rect, parent, id, lic_string = nothing)
clsid = string(_GetControlCLSID(self))
self.__dict__["_obj_"] = CreateControl(win32ui, clsid, windowTitle, style, rect, parent, id, nothing, false, lic_string)
klass = _GetDispatchClass(self)
dispobj = klass(GetIDispatchForWindow(win32uiole, self._obj_))
HookOleEvents(self)
self.__dict__["_dispobj_"] = dispobj
end

function HookOleEvents(self::Control)
dict = _GetEventMap(self)
for (dispid, methodName) in items(dict)
if hasfield(typeof(self), :methodName)
HookOleEvent(self._obj_, getfield(self, :methodName), dispid)
end
end
end

function __getattr__(self::Control, attr)
try
return __getattr__(window.Wnd, self)
catch exn
if exn isa AttributeError
#= pass =#
end
end
return getfield(self._dispobj_, :attr)
end

function __setattr__(self::Control, attr, value)
if hasfield(typeof(self.__dict__), :attr)
self.__dict__[attr] = value
return
end
try
if self._dispobj_
__setattr__(self._dispobj_, attr, value)
return
end
catch exn
if exn isa AttributeError
#= pass =#
end
end
self.__dict__[attr] = value
end

function MakeControlClass(controlClass, name = nothing)
#= Given a CoClass in a generated .py file, this function will return a Class
    object which can be used as an OCX control.

    This function is used when you do not want to handle any events from the OCX
    control.  If you need events, then you should derive a class from both the
    activex.Control class and the CoClass
     =#
if name === nothing
name = controlClass.__name__
end
return new_type("OCX" + name, (Control, controlClass), Dict())
end

function MakeControlInstance(controlClass, name = nothing)
#= As for MakeControlClass(), but returns an instance of the class. =#
return MakeControlClass(controlClass, name)()
end
