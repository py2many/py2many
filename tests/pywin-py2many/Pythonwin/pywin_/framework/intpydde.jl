using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")

import win32con
using win32com_.gen_py.mfc: object
using dde: *

abstract type AbstractDDESystemTopic <: Abstractobject.Object end
abstract type AbstractDDEServer <: Abstractobject.Object end
mutable struct DDESystemTopic <: AbstractDDESystemTopic
app

            DDESystemTopic(app) = begin
                object.Object.__init__(self, CreateServerSystemTopic())
                new(app)
            end
end
function Exec(self::DDESystemTopic, data)::Int64
try
OnDDECommand(self.app, data)
catch exn
t, v, tb = exc_info(sys)
println("Error executing DDE command.")
print_exception(traceback, t, v, tb)
return 0
end
end

mutable struct DDEServer <: AbstractDDEServer
app
topic
item

            DDEServer(app) = begin
                object.Object.__init__(self, CreateServer())
                new(app)
            end
end
function CreateSystemTopic(self::DDEServer)::DDESystemTopic
return DDESystemTopic(self.app)
end

function Shutdown(self::DDEServer)
Shutdown(self._obj_)
Destroy(self._obj_)
if self.topic != nothing
Destroy(self.topic)
self.topic = nothing
end
if self.item != nothing
Destroy(self.item)
self.item = nothing
end
end

function OnCreate(self::DDEServer)::Int64
return 1
end

function Status(self::DDEServer, msg)
try
SetStatusText(win32ui, msg)
catch exn
if exn isa win32ui.error
#= pass =#
end
end
end
