using Printf
using PyCall
using StringEncodings
win32ui = pyimport("win32ui")

using win32com_.gen_py.mfc: docview
using win32com_.gen_py: default_scintilla_encoding
include("scintillacon.jl")
import win32con
import string

import codecs

abstract type AbstractCScintillaDocument <: AbstractParentScintillaDocument end
abstract type AbstractViewNotifyDelegate end
abstract type AbstractDocumentNotifyDelegate end
crlf_bytes = encode("\r\n", "ascii")
lf_bytes = encode("\n", "ascii")
re_encoding_bytes = compile(re, encode("coding[:=]\\s*([-\\w.]+)", "ascii"))
re_encoding_text = compile(re, "coding[:=]\\s*([-\\w.]+)")
ParentScintillaDocument = docview.Document
mutable struct CScintillaDocument <: AbstractCScintillaDocument
#= A SyntEdit document. =#
bom
source_encoding

            CScintillaDocument() = begin
                ParentScintillaDocument.__init__(self, args...)
                new()
            end
end
function DeleteContents(self::CScintillaDocument)
#= pass =#
end

function OnOpenDocument(self::CScintillaDocument, filename)::Int64
SetPathName(self, filename)
try
f = readline(filename)
try
_LoadTextFromFile(self, f)
finally
close(f)
end
catch exn
if exn isa IOError
rc = MessageBox(win32ui, "Could not load the file from %s\n\nDo you want to create a new file?" % filename, "Pythonwin", win32con.MB_YESNO | win32con.MB_ICONWARNING)
if rc == win32con.IDNO
return 0
end
@assert(rc == win32con.IDYES)
try
f = readline(filename)
try
_LoadTextFromFile(self, f)
finally
close(f)
end
catch exn
 let e = exn
if e isa IOError
rc = MessageBox(win32ui, "Cannot create the file %s" % filename)
end
end
end
end
end
return 1
end

function SaveFile(self::CScintillaDocument, fileName, encoding = nothing)
view = GetFirstView(self)
ok = SaveTextFile(view, fileName, encoding)
if ok
SCISetSavePoint(view)
end
return ok
end

function ApplyFormattingStyles(self::CScintillaDocument)
_ApplyOptionalToViews(self, "ApplyFormattingStyles")
end

function _LoadTextFromFile(self::CScintillaDocument, f)
l = readline(f)
l2 = readline(f)
if endswith(l, crlf_bytes) || !endswith(l, lf_bytes)
eol_mode = scintillacon.SC_EOL_CRLF
else
eol_mode = scintillacon.SC_EOL_LF
end
has_break = false
for (bom, encoding) in ((codecs.BOM_UTF8, "utf8"), (codecs.BOM_UTF16_LE, "utf_16_le"), (codecs.BOM_UTF16_BE, "utf_16_be"))
if startswith(l, bom)
self.bom = bom
self.source_encoding = encoding
l = l[length(bom) + 1:end]
has_break = true
break;
end
end
if has_break != true
for look in (l, l2)
match = search(re_encoding_bytes, look)
if match != nothing
self.source_encoding = decode(group(match, 1), "ascii")
has_break = true
break;
end
end
end
text = (l + l2) + read(f)
source_encoding = self.source_encoding
if source_encoding === nothing
source_encoding = "utf-8"
end
try
dec = decode(text, source_encoding)
catch exn
if exn isa UnicodeError
@printf("WARNING: Failed to decode bytes from \'%s\' encoding - treating as latin1\n", source_encoding)
dec = decode(text, "latin1")
end
if exn isa LookupError
@printf("WARNING: Invalid encoding \'%s\' specified - treating as latin1\n", source_encoding)
dec = decode(text, "latin1")
end
end
text = encode(dec, default_scintilla_encoding)
view = GetFirstView(self)
if IsWindow(view)
SendScintilla(view, scintillacon.SCI_SETUNDOCOLLECTION, 0, 0)
SetReadOnly(view, 0)
SendScintilla(view, scintillacon.SCI_CLEARALL)
SendMessage(view, scintillacon.SCI_ADDTEXT, text)
SendScintilla(view, scintillacon.SCI_SETUNDOCOLLECTION, 1, 0)
SendScintilla(view, win32con.EM_EMPTYUNDOBUFFER, 0, 0)
SendScintilla(view, scintillacon.SCI_SETEOLMODE, eol_mode)
end
end

function _SaveTextToFile(self::CScintillaDocument, view, filename, encoding = nothing)
s = GetTextRange(view)
source_encoding = encoding
if source_encoding === nothing
if self.bom
source_encoding = self.source_encoding
else
bits = split(re, "[\r\n]+", s, 3)
for look in bits[begin:-1]
match = search(re_encoding_text, look)
if match != nothing
source_encoding = group(match, 1)
self.source_encoding = source_encoding
has_break = true
break;
end
end
end
if source_encoding === nothing
source_encoding = "utf-8"
end
end
file_contents = encode(s, source_encoding)
f = readline(filename)
try
if self.bom
write(f, self.bom)
end
write(f, file_contents)
finally
close(f)
end
SetModifiedFlag(self, 0)
end

function FinalizeViewCreation(self::CScintillaDocument, view)
#= pass =#
end

function HookViewNotifications(self::CScintillaDocument, view)
parent = GetParentFrame(view)
HookNotify(parent, ViewNotifyDelegate(self, "OnBraceMatch"), scintillacon.SCN_CHECKBRACE)
HookNotify(parent, ViewNotifyDelegate(self, "OnMarginClick"), scintillacon.SCN_MARGINCLICK)
HookNotify(parent, ViewNotifyDelegate(self, "OnNeedShown"), scintillacon.SCN_NEEDSHOWN)
HookNotify(parent, DocumentNotifyDelegate(self, "OnSavePointReached"), scintillacon.SCN_SAVEPOINTREACHED)
HookNotify(parent, DocumentNotifyDelegate(self, "OnSavePointLeft"), scintillacon.SCN_SAVEPOINTLEFT)
HookNotify(parent, DocumentNotifyDelegate(self, "OnModifyAttemptRO"), scintillacon.SCN_MODIFYATTEMPTRO)
SCIAutoCStops(view, string.whitespace + "()[]:;+-/*=\\?\'!#@\$%^&,<>\"\'|")
if view != GetFirstView(self)
SCISetDocPointer(view, SCIGetDocPointer(GetFirstView(self)))
end
end

function OnSavePointReached(self::CScintillaDocument, std, extra)
SetModifiedFlag(self, 0)
end

function OnSavePointLeft(self::CScintillaDocument, std, extra)
SetModifiedFlag(self, 1)
end

function OnModifyAttemptRO(self::CScintillaDocument, std, extra)
MakeDocumentWritable(self)
end

function MarkerAdd(self::CScintillaDocument, lineNo, marker)
SCIMarkerAdd(GetEditorView(self), lineNo - 1, marker)
end

function MarkerCheck(self::CScintillaDocument, lineNo, marker)::Bool
v = GetEditorView(self)
lineNo = lineNo - 1
markerState = SCIMarkerGet(v, lineNo)
return (markerState & (1 << marker)) != 0
end

function MarkerToggle(self::CScintillaDocument, lineNo, marker)
v = GetEditorView(self)
if MarkerCheck(self, lineNo, marker)
SCIMarkerDelete(v, lineNo - 1, marker)
else
SCIMarkerAdd(v, lineNo - 1, marker)
end
end

function MarkerDelete(self::CScintillaDocument, lineNo, marker)
SCIMarkerDelete(GetEditorView(self), lineNo - 1, marker)
end

function MarkerDeleteAll(self::CScintillaDocument, marker)
SCIMarkerDeleteAll(GetEditorView(self), marker)
end

function MarkerGetNext(self::CScintillaDocument, lineNo, marker)::Int64
return SCIMarkerNext(GetEditorView(self), lineNo - 1, 1 << marker) + 1
end

function MarkerAtLine(self::CScintillaDocument, lineNo, marker)::Int64
markerState = SCIMarkerGet(GetEditorView(self), lineNo - 1)
return markerState & (1 << marker)
end

function _ApplyToViews(self::CScintillaDocument, funcName)
for view in GetAllViews(self)
func = getfield(view, :funcName)
func(args...)
end
end

function _ApplyOptionalToViews(self::CScintillaDocument, funcName)
for view in GetAllViews(self)
func = (hasfield(typeof(view), :funcName) ? 
                getfield(view, :funcName) : nothing)
if func != nothing
func(args...)
end
end
end

function GetEditorView(self::CScintillaDocument)
try
frame_gev = GetParentFrame(GetFirstView(self)).GetEditorView
catch exn
if exn isa AttributeError
return GetFirstView(self)
end
end
return frame_gev()
end

mutable struct ViewNotifyDelegate <: AbstractViewNotifyDelegate
doc
name
end
function __call__(self::ViewNotifyDelegate, std, extra)
hwndFrom, idFrom, code = std
for v in GetAllViews(self.doc)
if GetSafeHwnd(v) === hwndFrom
return getfield(v, :self.name)((std, extra)...)
end
end
end

mutable struct DocumentNotifyDelegate <: AbstractDocumentNotifyDelegate
doc
delegate
end
function __call__(self::DocumentNotifyDelegate, std, extra)
hwndFrom, idFrom, code = std
if hwndFrom == GetSafeHwnd(GetEditorView(self.doc))
delegate(self, (std, extra)...)
end
end
