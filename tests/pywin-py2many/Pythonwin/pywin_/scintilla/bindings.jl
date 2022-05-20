using OrderedCollections
using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
include("IDLEenvironment.jl")
import string


import win32con
include("keycodes.jl")


abstract type AbstractSendCommandHandler end
abstract type AbstractBinding end
abstract type AbstractBindingsManager end
HANDLER_ARGS_GUESS = 0
HANDLER_ARGS_NATIVE = 1
HANDLER_ARGS_IDLE = 2
HANDLER_ARGS_EXTENSION = 3
next_id = 5000
event_to_commands = Dict()
command_to_events = OrderedDict()
function assign_command_id(event, id = 0)
global next_id
if id == 0
id = get(event_to_commands, event, 0)
if id == 0
id = next_id
next_id = next_id + 1
end
command_to_events[id] = event
end
event_to_commands[event] = id
return id
end

mutable struct SendCommandHandler <: AbstractSendCommandHandler
cmd
end
function __call__(self::SendCommandHandler)
SendMessage(GetMainFrame(win32ui), win32con.WM_COMMAND, self.cmd)
end

mutable struct Binding <: AbstractBinding
handler
handler_args_type
end

mutable struct BindingsManager <: AbstractBindingsManager
parent_view
bindings::Dict
keymap::Dict
_OnCommand
end
function prepare_configure(self::BindingsManager)
self.keymap = Dict()
end

function complete_configure(self::BindingsManager)
for id in keys(command_to_events)
HookCommand(self.parent_view, self._OnCommand, id)
end
end

function close(self::BindingsManager)
self.parent_view = nothing
self.bindings = nothing
self.keymap = nothing
end

function report_error(self::BindingsManager, problem)
try
SetStatusText(win32ui, problem, 1)
catch exn
if exn isa win32ui.error
println(problem)
end
end
end

function update_keymap(self::BindingsManager, keymap)
update(self.keymap, keymap)
end

function bind(self::BindingsManager, event, handler, handler_args_type = HANDLER_ARGS_GUESS, cid = 0)
if handler === nothing
handler = SendCommandHandler(cid)
end
self.bindings[event] = _new_binding(self, handler, handler_args_type)
bind_command(self, event, cid)
end

function bind_command(self::BindingsManager, event, id = 0)
#= Binds an event to a Windows control/command ID =#
id = assign_command_id(event, id)
return id
end

function get_command_id(self::BindingsManager, event)
id = get(event_to_commands, event)
if id === nothing
if event ∉ self.bindings
return nothing
end
id = bind_command(self, event)
end
return id
end

function _OnCommand(self::BindingsManager, id, code)::Int64
event = get(command_to_events, id)
if event === nothing
report_error(self, "No event associated with event ID %d" % id)
return 1
end
return fire(self, event)
end

function _new_binding(self::BindingsManager, event, handler_args_type)::Binding
return Binding(event, handler_args_type)
end

function _get_IDLE_handler(self::BindingsManager, ext, handler)
try
instance = IDLEExtension(self.parent_view.idle, ext)
name = replace(handler, "-", "_") + "_event"
return getfield(instance, :name)
catch exn
if exn isa (ImportError, AttributeError)
msg = "Can not find event \'%s\' in IDLE extension \'%s\'" % (handler, ext)
report_error(self, msg)
return nothing
end
end
end

function fire(self::BindingsManager, event, event_param = nothing)::Int64
binding = get(self.bindings, event)
if binding === nothing
handler = (hasfield(typeof(self.parent_view), :event+Event) ? 
                getfield(self.parent_view, :event+Event) : nothing)
if handler === nothing
report_error(self, "The event name \'%s\' can not be found." % event)
return 1
end
binding = _new_binding(self, handler, HANDLER_ARGS_NATIVE)
self.bindings[event] = binding
end
handler_args_type = binding.handler_args_type
if handler_args_type == HANDLER_ARGS_GUESS
if event[1] == "<"
handler_args_type = HANDLER_ARGS_IDLE
else
handler_args_type = HANDLER_ARGS_EXTENSION
end
end
try
if handler_args_type == HANDLER_ARGS_EXTENSION
args = (self.parent_view.idle, event_param)
else
args = (event_param,)
end
rc = handler(binding, args...)
if handler_args_type == HANDLER_ARGS_IDLE
if rc ∈ [nothing, "break"]
rc = 0
else
rc = 1
end
end
catch exn
message = "Firing event \'%s\' failed." % event
println(message)
current_exceptions() != [] ? current_exceptions()[end] : nothing
report_error(self, message)
rc = 1
end
return rc
end

function fire_key_event(self::BindingsManager, msg)::Int64
key = msg[3]
keyState = 0
if GetKeyState(win32api, win32con.VK_CONTROL) & 32768
keyState = (keyState | win32con.RIGHT_CTRL_PRESSED) | win32con.LEFT_CTRL_PRESSED
end
if GetKeyState(win32api, win32con.VK_SHIFT) & 32768
keyState = keyState | win32con.SHIFT_PRESSED
end
if GetKeyState(win32api, win32con.VK_MENU) & 32768
keyState = (keyState | win32con.LEFT_ALT_PRESSED) | win32con.RIGHT_ALT_PRESSED
end
keyinfo = (key, keyState)
event = get(self.keymap, keyinfo)
if event === nothing
return 1
end
return fire(self, event, nothing)
end
