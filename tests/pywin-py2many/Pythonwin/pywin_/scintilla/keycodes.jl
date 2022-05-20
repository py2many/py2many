using Printf
using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
import string
import win32con


MAPVK_VK_TO_CHAR = 2
key_name_to_vk = Dict()
key_code_to_name = Dict()
_better_names = Dict("escape" => "esc", "return" => "enter", "back" => "pgup", "next" => "pgdn")
function _fillvkmap()
names = [entry for entry in win32con.__dict__ if startswith(entry, "VK_") ]
for name in names
code = getfield(win32con, :name)
n = lower(name[4:end])
key_name_to_vk[n] = code
if n ∈ keys(_better_names)
n = _better_names[n]
key_name_to_vk[n] = code
end
key_code_to_name[code] = n
end
end

_fillvkmap()
function get_vk(chardesc)
if length(chardesc) == 1
info = VkKeyScan(win32api, chardesc)
if info == -1
return (0, 0)
end
vk = LOBYTE(win32api, info)
state = HIBYTE(win32api, info)
modifiers = 0
if state & 1
modifiers |= win32con.SHIFT_PRESSED
end
if state & 2
modifiers |= win32con.LEFT_CTRL_PRESSED | win32con.RIGHT_CTRL_PRESSED
end
if state & 4
modifiers |= win32con.LEFT_ALT_PRESSED | win32con.RIGHT_ALT_PRESSED
end
return (vk, modifiers)
end
return (get(key_name_to_vk, lower(chardesc)), 0)
end

modifiers = Dict("alt" => win32con.LEFT_ALT_PRESSED | win32con.RIGHT_ALT_PRESSED, "lalt" => win32con.LEFT_ALT_PRESSED, "ralt" => win32con.RIGHT_ALT_PRESSED, "ctrl" => win32con.LEFT_CTRL_PRESSED | win32con.RIGHT_CTRL_PRESSED, "ctl" => win32con.LEFT_CTRL_PRESSED | win32con.RIGHT_CTRL_PRESSED, "control" => win32con.LEFT_CTRL_PRESSED | win32con.RIGHT_CTRL_PRESSED, "lctrl" => win32con.LEFT_CTRL_PRESSED, "lctl" => win32con.LEFT_CTRL_PRESSED, "rctrl" => win32con.RIGHT_CTRL_PRESSED, "rctl" => win32con.RIGHT_CTRL_PRESSED, "shift" => win32con.SHIFT_PRESSED, "key" => 0)
function parse_key_name(name)
name = name + "-"
start = 0
pos = 0
max = length(name)
toks = []
while pos < max
if name[pos + 1] ∈ "+-"
tok = name[start + 1:pos]
push!(toks, lower(tok))
pos += 1
start = pos
end
pos += 1
end
flags = 0
for tok in toks[begin:-1]
mod = get(modifiers, lower(tok))
if mod != nothing
flags |= mod
end
end
vk, this_flags = get_vk(toks[end])
return (vk, flags | this_flags)
end

_checks = [[("Shift", win32con.SHIFT_PRESSED)], [("Ctrl", win32con.LEFT_CTRL_PRESSED | win32con.RIGHT_CTRL_PRESSED), ("LCtrl", win32con.LEFT_CTRL_PRESSED), ("RCtrl", win32con.RIGHT_CTRL_PRESSED)], [("Alt", win32con.LEFT_ALT_PRESSED | win32con.RIGHT_ALT_PRESSED), ("LAlt", win32con.LEFT_ALT_PRESSED), ("RAlt", win32con.RIGHT_ALT_PRESSED)]]
function make_key_name(vk, flags)
flags_done = 0
parts = []
for moddata in _checks
for (name, checkflag) in moddata
if flags & checkflag
push!(parts, name)
flags_done = flags_done & checkflag
has_break = true
break;
end
end
end
if flags_done & flags
push!(parts, hex(flags & ~(flags_done)))
end
if vk === nothing
push!(parts, "<Unknown scan code>")
else
try
push!(parts, key_code_to_name[vk])
catch exn
if exn isa KeyError
scancode = MapVirtualKey(win32api, vk, MAPVK_VK_TO_CHAR)
push!(parts, Char(scancode))
end
end
end
sep = "+"
if sep ∈ parts
sep = "-"
end
return join([capitalize(p) for p in parts], sep)
end

function _psc(char)
sc, mods = get_vk(char)
@printf("Char %s -> %d -> %s\n", repr(char), sc, get(key_code_to_name, sc))
end

function test1()
for ch in "aA0/?[{}];:\'\"`~_-+=\\|,<.>/?"
_psc(ch)
end
for code in ["Home", "End", "Left", "Right", "Up", "Down", "Menu", "Next"]
_psc(code)
end
end

function _pkn(n)
vk, flags = parse_key_name(n)
@printf("%s -> %s,%s -> %s\n", n, vk, flags, make_key_name(vk, flags))
end

function test2()
_pkn("ctrl+alt-shift+x")
_pkn("ctrl-home")
_pkn("Shift-+")
_pkn("Shift--")
_pkn("Shift+-")
_pkn("Shift++")
_pkn("LShift-+")
_pkn("ctl+home")
_pkn("ctl+enter")
_pkn("alt+return")
_pkn("Alt+/")
_pkn("Alt+BadKeyName")
_pkn("A")
_pkn("a")
_pkn("Shift-A")
_pkn("Shift-a")
_pkn("a")
_pkn("(")
_pkn("Ctrl+(")
_pkn("Ctrl+Shift-8")
_pkn("Ctrl+*")
_pkn("{")
_pkn("!")
_pkn(".")
end

if abspath(PROGRAM_FILE) == @__FILE__
test2()
end