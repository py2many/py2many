using OrderedCollections
using Printf
using PyCall
using StringEncodings
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
import win32com_.gen_py.framework.editor

import string


import win32con

using win32com_.gen_py.mfc.dialog: GetSimpleInput
using win32com_.gen_py: default_scintilla_encoding
wordchars = (string.ascii_uppercase + string.ascii_lowercase) + string.digits
abstract type AbstractTextError <: AbstractException end
abstract type AbstractEmptyRange <: AbstractException end
abstract type AbstractIDLEEditorWindow end
abstract type AbstractCallTips end
abstract type AbstractTkText end
abstract type AbstractIDLEWrapper end
mutable struct TextError <: AbstractTextError

end

mutable struct EmptyRange <: AbstractEmptyRange

end

function GetIDLEModule(module_)
try
modname = "win32com_.gen_py.idle." + module_
__import__(modname)
catch exn
 let details = exn
if details isa ImportError
msg = "The IDLE extension \'%s\' can not be located.\r\n\r\nPlease correct the installation and restart the application.\r\n\r\n%s" % (module_, details)
MessageBox(win32ui, msg)
return nothing
end
end
end
mod = sys.modules[modname + 1]
mod.TclError = TextError
return mod
end

function fast_readline(self::IDLEWrapper)
if self.finished
val = ""
else
if "_scint_lines" ∉ self.__dict__
self._scint_lines = split(GetTextRange(self.text.edit), "\n")
end
sl = self._scint_lines
i = self.i + 1
self.i = self.i + 1
if i >= length(sl)
val = ""
else
val = sl[i + 1] + "\n"
end
end
return encode(val, default_scintilla_encoding)
end

try
GetIDLEModule("AutoIndent").IndentSearcher.readline = fast_readline
catch exn
if exn isa AttributeError
#= pass =#
end
end
mutable struct IDLEEditorWindow <: AbstractIDLEEditorWindow
edit
text::AbstractTkText
extensions::Dict
extension_menus::Dict
end
function close(self::IDLEEditorWindow)
self.edit = nothing
self.text = nothing
self.extension_menus = nothing
try
for ext in values(self.extensions)
closer = (hasfield(typeof(ext), :close) ? 
                getfield(ext, :close) : nothing)
if closer != nothing
closer()
end
end
finally
self.extensions = OrderedDict()
end
end

function IDLEExtension(self::IDLEEditorWindow, extension)
ext = get(self.extensions, extension)
if ext != nothing
return ext
end
mod = GetIDLEModule(extension)
if mod === nothing
return nothing
end
klass = getfield(mod, :extension)
ext = klass(self)
self.extensions[extension] = klass(self)
events = [item for item in dir(klass) if item[length(item) - -5:end] == "_event" ]
for event in events
name = "<<%s>>" % (replace(event[begin:-6], "_", "-"),)
bind(self.edit.bindings, name, getfield(ext, :event))
end
return ext
end

function GetMenuItems(self::IDLEEditorWindow, menu_name)::Vector
bindings = self.edit.bindings
ret = []
for ext in values(self.extensions)
menudefs = (hasfield(typeof(ext), :menudefs) ? 
                getfield(ext, :menudefs) : [])
for (name, items) in menudefs
if name == menu_name
for (text, event) in [item for item in items if item != nothing ]
text = replace(text, "&", "&&")
text = replace(text, "_", "&")
push!(ret, (text, event))
end
end
end
end
return ret
end

function askinteger(self::IDLEEditorWindow, caption, prompt, parent = nothing, initialvalue = 0, minvalue = nothing, maxvalue = nothing)::Int64
while true
rc = GetSimpleInput(prompt, string(initialvalue), caption)
if rc === nothing
return 0
end
err = nothing
try
rc = parse(Int, rc)
catch exn
if exn isa ValueError
err = "Please enter an integer"
end
end
if !(err) && minvalue != nothing && rc < minvalue
err = "Please enter an integer greater then or equal to %s" % (minvalue,)
end
if !(err) && maxvalue != nothing && rc > maxvalue
err = "Please enter an integer less then or equal to %s" % (maxvalue,)
end
if err
MessageBox(win32ui, err, caption, win32con.MB_OK)
continue;
end
return rc
end
end

function askyesno(self::IDLEEditorWindow, caption, prompt, parent = nothing)::Bool
return MessageBox(win32ui, prompt, caption, win32con.MB_YESNO) == win32con.IDYES
end

function is_char_in_string(self::IDLEEditorWindow, text_index)::Int64
text_index = _getoffset(self.text, text_index)
c = _GetColorizer(self.text.edit)
if c && GetStringStyle(c, text_index) === nothing
return 0
end
return 1
end

function get_selection_indices(self::IDLEEditorWindow)::Tuple
try
first = index(self.text, "sel.first")
last = index(self.text, "sel.last")
return (first, last)
catch exn
if exn isa TextError
return (nothing, nothing)
end
end
end

function set_tabwidth(self::IDLEEditorWindow, width)
SCISetTabWidth(self.edit, width)
end

function get_tabwidth(self::IDLEEditorWindow)
return GetTabWidth(self.edit)
end

mutable struct CallTips <: AbstractCallTips
edit
end
function showtip(self::CallTips, tip_text)
SCICallTipShow(self.edit, tip_text)
end

function hidetip(self::CallTips)
SCICallTipCancel(self.edit)
end

function TkOffsetToIndex(offset, edit)
lineoff = 0
offset = min(offset, GetTextLength(edit))
line = LineFromChar(edit, offset)
lineIndex = LineIndex(edit, line)
return "%d.%d" % (line + 1, offset - lineIndex)
end

function _NextTok(str, pos)::Tuple
end_ = length(str)
if pos >= end_
return (nothing, 0)
end
while pos < end_ && str[pos + 1] ∈ string.whitespace
pos = pos + 1
end
if str[pos + 1] ∈ "+-"
return (str[pos + 1], pos + 1)
end
endPos = pos
while endPos < end_ && str[endPos + 1] ∈ (string.digits + ".")
endPos = endPos + 1
end
if pos != endPos
return (str[pos + 1:endPos], endPos)
end
endPos = pos
while endPos < end_ && str[endPos + 1] ∉ ((string.whitespace + string.digits) + "+-")
endPos = endPos + 1
end
if pos != endPos
return (str[pos + 1:endPos], endPos)
end
return (nothing, 0)
end

function TkIndexToOffset(bm, edit, marks)
base, nextTokPos = _NextTok(bm, 0)
if base === nothing
throw(ValueError("Empty bookmark ID!"))
end
if find(base, ".") > 0
try
line, col = split(base, ".", 2)
if col == "first" || col == "last"
if line != "sel"
throw(ValueError("Tags arent here!"))
end
sel = GetSel(edit)
if sel[1] == sel[2]
throw(EmptyRange)
end
if col == "first"
pos = sel[1]
else
pos = sel[2]
end
else
line = Int(line) - 1
if line > GetLineCount(edit)
pos = GetTextLength(edit) + 1
else
pos = LineIndex(edit, line)
if pos == -1
pos = GetTextLength(edit)
end
pos = pos + parse(Int, col)
end
end
catch exn
if exn isa (ValueError, IndexError)
throw(ValueError("Unexpected literal in \'%s\'" % base))
end
end
elseif base == "insert"
pos = GetSel(edit)[1]
elseif base == "end"
pos = GetTextLength(edit)
if pos && SCIGetCharAt(edit, pos - 1) != "\n"
pos = pos + 1
end
else
try
pos = marks[base + 1]
catch exn
if exn isa KeyError
throw(ValueError("Unsupported base offset or undefined mark \'%s\'" % base))
end
end
end
while true
word, nextTokPos = _NextTok(bm, nextTokPos)
if word === nothing
has_break = true
break;
end
if word ∈ ["+", "-"]
num, nextTokPos = _NextTok(bm, nextTokPos)
if num === nothing
throw(ValueError("+/- operator needs 2 args"))
end
what, nextTokPos = _NextTok(bm, nextTokPos)
if what === nothing
throw(ValueError("+/- operator needs 2 args"))
end
if what[1] != "c"
throw(ValueError("+/- only supports chars"))
end
if word == "+"
pos = pos + parse(Int, num)
else
pos = pos - parse(Int, num)
end
elseif word == "wordstart"
while pos > 0 && SCIGetCharAt(edit, pos - 1) ∈ wordchars
pos = pos - 1
end
elseif word == "wordend"
end_ = GetTextLength(edit)
while pos < end_ && SCIGetCharAt(edit, pos) ∈ wordchars
pos = pos + 1
end
elseif word == "linestart"
while pos > 0 && SCIGetCharAt(edit, pos - 1) ∉ "\n\r"
pos = pos - 1
end
elseif word == "lineend"
end_ = GetTextLength(edit)
while pos < end_ && SCIGetCharAt(edit, pos) ∉ "\n\r"
pos = pos + 1
end
else
throw(ValueError("Unsupported relative offset \'%s\'" % word))
end
end
return max(pos, 0)
end

mutable struct TkText <: AbstractTkText
calltips
edit
marks::Dict
end
function make_calltip_window(self::TkText)
if self.calltips === nothing
self.calltips = CallTips(self.edit)
end
return self.calltips
end

function _getoffset(self::TkText, index)
return TkIndexToOffset(index, self.edit, self.marks)
end

function _getindex(self::TkText, off)
return TkOffsetToIndex(off, self.edit)
end

function _fix_indexes(self::TkText, start, end_)::Tuple
while start > 0 && (Int(codepoint(SCIGetCharAt(self.edit, start))) & 192) == 128
start -= 1
end
while end_ < GetTextLength(self.edit) && (Int(codepoint(SCIGetCharAt(self.edit, end_))) & 192) == 128
end_ += 1
end
if start > 0 && SCIGetCharAt(self.edit, start) == "\n" && SCIGetCharAt(self.edit, start - 1) == "\r"
start = start - 1
end
if end_ < GetTextLength(self.edit) && SCIGetCharAt(self.edit, end_ - 1) == "\r" && SCIGetCharAt(self.edit, end_) == "\n"
end_ = end_ + 1
end
return (start, end_)
end

function bind(self::TkText, binding, handler)
bind(self.edit.bindings, binding, handler)
end

function get(self::TkText, start, end_ = nothing)::String
try
start = _getoffset(self, start)
if end_ === nothing
end_ = start + 1
else
end_ = _getoffset(self, end_)
end
catch exn
if exn isa EmptyRange
return ""
end
end
if end_ <= start
return ""
end
max = GetTextLength(self.edit)
checkEnd = 0
if end_ > max
end_ = max
checkEnd = 1
end
start, end_ = _fix_indexes(self, start, end_)
ret = GetTextRange(self.edit, start, end_)
if checkEnd && !(ret) || ret[end] != "\n"
ret = ret * "\n"
end
return replace(ret, "\r", "")
end

function index(self::TkText, spec)::String
try
return _getindex(self, _getoffset(self, spec))
catch exn
if exn isa EmptyRange
return ""
end
end
end

function insert(self::TkText, pos, text)
try
pos = _getoffset(self, pos)
catch exn
if exn isa EmptyRange
throw(TextError("Empty range"))
end
end
SetSel(self.edit, (pos, pos))
bits = split(text, "\n")
SCIAddText(self.edit, bits[1])
for bit in bits[2:end]
SCINewline(self.edit)
SCIAddText(self.edit, bit)
end
end

function delete(self::TkText, start, end_ = nothing)
try
start = _getoffset(self, start)
if end_ != nothing
end_ = _getoffset(self, end_)
end
catch exn
if exn isa EmptyRange
throw(TextError("Empty range"))
end
end
if start == end_
return
end
if end_ === nothing
end_ = start + 1
elseif end_ < start
return
end
if start == GetTextLength(self.edit)
return
end
old = GetSel(self.edit)[1]
start, end_ = _fix_indexes(self, start, end_)
SetSel(self.edit, (start, end_))
Clear(self.edit)
if old >= start && old < end_
old = start
elseif old >= end_
old = old - (end_ - start)
end
SetSel(self.edit, old)
end

function bell(self::TkText)
MessageBeep(win32api)
end

function see(self::TkText, pos)
#= pass =#
end

function mark_set(self::TkText, name, pos)
try
pos = _getoffset(self, pos)
catch exn
if exn isa EmptyRange
throw(TextError("Empty range \'%s\'" % pos))
end
end
if name == "insert"
SetSel(self.edit, pos)
else
self.marks[name] = pos
end
end

function tag_add(self::TkText, name, start, end_)
if name != "sel"
throw(ValueError("Only sel tag is supported"))
end
try
start = _getoffset(self, start)
end_ = _getoffset(self, end_)
catch exn
if exn isa EmptyRange
throw(TextError("Empty range"))
end
end
SetSel(self.edit, start, end_)
end

function tag_remove(self::TkText, name, start, end_)
if name != "sel" || start != "1.0" || end_ != "end"
throw(ValueError("Cant remove this tag"))
end
SetSel(self.edit, GetSel(self.edit)[1])
end

function compare(self::TkText, i1, op, i2)
try
i1 = _getoffset(self, i1)
catch exn
if exn isa EmptyRange
i1 = ""
end
end
try
i2 = _getoffset(self, i2)
catch exn
if exn isa EmptyRange
i2 = ""
end
end
return eval("%d%s%d" % (i1, op, i2))
end

function undo_block_start(self::TkText)
SCIBeginUndoAction(self.edit)
end

function undo_block_stop(self::TkText)
SCIEndUndoAction(self.edit)
end

function TestCheck(index, edit, expected = nothing)
rc = TkIndexToOffset(index, edit, Dict())
if rc != expected
println("ERROR: Index$(index), expected$(expected)but got$(rc)")
end
end

function TestGet(fr, to, t, expected)
got = get(t, fr, to)
if got != expected
@printf("ERROR: get(%s, %s) expected %s, but got %s\n", repr(fr), repr(to), repr(expected), repr(got))
end
end

function test()
d = OpenDocumentFile(win32com_.gen_py.framework.editor.editorTemplate, nothing)
e = GetFirstView(d)
t = TkText(e)
SCIAddText(e, "hi there how\nare you today\r\nI hope you are well")
SetSel(e, (4, 4))
skip = "\n\tTestCheck(\"insert\", e, 4)\n\tTestCheck(\"insert wordstart\", e, 3)\n\tTestCheck(\"insert wordend\", e, 8)\n\tTestCheck(\"insert linestart\", e, 0)\n\tTestCheck(\"insert lineend\", e, 12)\n\tTestCheck(\"insert + 4 chars\", e, 8)\n\tTestCheck(\"insert +4c\", e, 8)\n\tTestCheck(\"insert - 2 chars\", e, 2)\n\tTestCheck(\"insert -2c\", e, 2)\n\tTestCheck(\"insert-2c\", e, 2)\n\tTestCheck(\"insert-2 c\", e, 2)\n\tTestCheck(\"insert- 2c\", e, 2)\n\tTestCheck(\"1.1\", e, 1)\n\tTestCheck(\"1.0\", e, 0)\n\tTestCheck(\"2.0\", e, 13)\n\ttry:\n\t\tTestCheck(\"sel.first\", e, 0)\n\t\tprint \"*** sel.first worked with an empty selection\"\n\texcept TextError:\n\t\tpass\n\te.SetSel((4,5))\n\tTestCheck(\"sel.first- 2c\", e, 2)\n\tTestCheck(\"sel.last- 2c\", e, 3)\n\t"
SetSel(e, (4, 4))
TestGet("insert lineend", "insert lineend +1c", t, "\n")
SetSel(e, (20, 20))
TestGet("insert lineend", "insert lineend +1c", t, "\n")
SetSel(e, (35, 35))
TestGet("insert lineend", "insert lineend +1c", t, "\n")
end

mutable struct IDLEWrapper <: AbstractIDLEWrapper
text
end

function IDLETest(extension)
modname = "win32com_.gen_py.idle." + extension
__import__(modname)
mod = sys.modules[modname + 1]
mod.TclError = TextError
klass = getfield(mod, :extension)
d = OpenDocumentFile(win32com_.gen_py.framework.editor.editorTemplate, nothing)
v = GetFirstView(d)
fname = splitext(os.path, __file__)[1] + ".py"
SCIAddText(v, read(readline(fname)))
SetModifiedFlag(d, 0)
r = klass(IDLEWrapper(TkText(v)))
return r
end

if abspath(PROGRAM_FILE) == @__FILE__
test()
end