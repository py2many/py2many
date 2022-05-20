using Printf
import CallTipWindow
import __main__
import string

import inspect

abstract type AbstractCallTips end
abstract type AbstractTC end
mutable struct CallTips <: AbstractCallTips
_make_calltip_window
calltip
calltip_start
editwin
text
keydefs::Dict{String, Vector{String}}
menudefs::Vector
unix_keydefs::Dict
windows_keydefs::Dict

            CallTips(editwin, keydefs::Dict{String, Vector{String}} = Dict("<<paren-open>>" => ["<Key-parenleft>"], "<<paren-close>>" => ["<Key-parenright>"], "<<check-calltip-cancel>>" => ["<KeyRelease>"], "<<calltip-cancel>>" => ["<ButtonPress>", "<Key-Escape>"]), menudefs::Vector = [], unix_keydefs::Dict = Dict(), windows_keydefs::Dict = Dict()) = begin
                if hasfield(typeof(text), :make_calltip_window)
_make_calltip_window = text.make_calltip_window
else
_make_calltip_window = _make_tk_calltip_window
end
                new(editwin, keydefs, menudefs, unix_keydefs, windows_keydefs)
            end
end
function close(self::CallTips)
self._make_calltip_window = nothing
end

function _make_tk_calltip_window(self::CallTips)
return CallTip(CallTipWindow, self.text)
end

function _remove_calltip_window(self::CallTips)
if self.calltip
hidetip(self.calltip)
self.calltip = nothing
end
end

function paren_open_event(self::CallTips, event)::String
_remove_calltip_window(self)
arg_text = get_arg_text(get_object_at_cursor(self))
if arg_text
self.calltip_start = index(self.text, "insert")
self.calltip = _make_calltip_window(self)
showtip(self.calltip, arg_text)
end
return ""
end

function paren_close_event(self::CallTips, event)::String
_remove_calltip_window(self)
return ""
end

function check_calltip_cancel_event(self::CallTips, event)::String
if self.calltip
if compare(self.text, "insert", "<=", self.calltip_start) || compare(self.text, "insert", ">", self.calltip_start + " lineend")
_remove_calltip_window(self)
end
end
return ""
end

function calltip_cancel_event(self::CallTips, event)::String
_remove_calltip_window(self)
return ""
end

function get_object_at_cursor(self::CallTips, wordchars = (("._" + string.ascii_uppercase) + string.ascii_lowercase) + string.digits)
text = self.text
chars = get(text, "insert linestart", "insert")
i = length(chars)
while i && chars[i] ∈ wordchars
i = i - 1
end
word = chars[i + 1:end]
if word
namespace = copy(sys.modules)
update(namespace, __main__.__dict__)
try
return eval(word, namespace)
catch exn
#= pass =#
end
end
return nothing
end

function _find_constructor(class_ob)
try
return class_ob.__init__
catch exn
if exn isa AttributeError
for base in class_ob.__bases__
rc = _find_constructor(base)
if rc != nothing
return rc
end
end
end
end
return nothing
end

function get_arg_text(ob)::String
argText = ""
if ob != nothing
argOffset = 0
if isclass(inspect, ob)
fob = _find_constructor(ob)
if fob === nothing
fob = () -> nothing
end
else
fob = ob
end
if isfunction(inspect, fob) || ismethod(inspect, fob)
try
arg_getter = (hasfield(typeof(inspect), :getfullargspec) ? 
                getfield(inspect, :getfullargspec) : inspect.getargspec)
argText = formatargspec(inspect, arg_getter(fob)...)
catch exn
println("Failed to format the args")
current_exceptions() != [] ? current_exceptions()[end] : nothing
end
end
if hasfield(typeof(ob), :__doc__)
doc = ob.__doc__
try
doc = strip(doc)
pos = find(doc, "\n")
catch exn
if exn isa AttributeError
#= pass =#
end
end
end
end
return argText
end

if abspath(PROGRAM_FILE) == @__FILE__
function t1()
#= () =#
end

function t2(a, b = nothing)
#= (a, b=None) =#
end

function t3(a)
#= (a, *args) =#
end

function t4()
#= (*args) =#
end

function t5(a)
#= (a, *args) =#
end

function t6(a, b = nothing)
#= (a, b=None, *args, **kw) =#
end

mutable struct TC <: AbstractTC
#= (self, a=None, *b) =#
a

                    TC(a = nothing) =
                        new(a)
end
function t1(self::TC)
#= (self) =#
end

function t2(self::TC, a, b = nothing)
#= (self, a, b=None) =#
end

function t3(self::TC, a)
#= (self, a, *args) =#
end

function t4(self::TC)
#= (self, *args) =#
end

function t5(self::TC, a)
#= (self, a, *args) =#
end

function t6(self::TC, a, b = nothing)
#= (self, a, b=None, *args, **kw) =#
end

function test(tests)
failed = []
for t in tests
expected = (t.__doc__ + "\n") + t.__doc__
if get_arg_text(t) != expected
push!(failed, t)
@printf("%s - expected %s, but got %s\n", t, repr(expected), repr(get_arg_text(t)))
end
end
@printf("%d of %d tests failed\n", length(failed), length(tests))
end

tc = TC()
tests = (t1, t2, t3, t4, t5, t6, TC, tc.t1, tc.t2, tc.t3, tc.t4, tc.t5, tc.t6)
test(tests)
end