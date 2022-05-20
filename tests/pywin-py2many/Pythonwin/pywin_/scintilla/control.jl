using PyCall
using StringEncodings
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
include("formatter.jl")
using win32com_.gen_py.mfc: window
using win32com_.gen_py: default_scintilla_encoding
import win32con




import string

include("scintillacon.jl")
abstract type AbstractScintillaNotification end
abstract type AbstractScintillaControlInterface end
abstract type AbstractCScintillaEditInterface <: AbstractScintillaControlInterface end
abstract type AbstractCScintillaColorEditInterface <: AbstractCScintillaEditInterface end
abstract type AbstractCScintillaEdit <: Abstractwindow.Wnd end
dllid = nothing
if win32ui.debug
try
dllid = LoadLibrary(win32api, join)
catch exn
if exn isa win32api.error
#= pass =#
end
end
end
if dllid === nothing
try
dllid = LoadLibrary(win32api, join)
catch exn
if exn isa win32api.error
#= pass =#
end
end
end
if dllid === nothing
dllid = LoadLibrary(win32api, "Scintilla.DLL")
end
null_byte = encode("\000", "ascii")
EM_GETTEXTRANGE = 1099
EM_EXLINEFROMCHAR = 1078
EM_FINDTEXTEX = 1103
EM_GETSELTEXT = 1086
EM_EXSETSEL = win32con.WM_USER + 55
mutable struct ScintillaNotification <: AbstractScintillaNotification


            ScintillaNotification() = begin
                __dict__.update(args)
                new()
            end
end

mutable struct ScintillaControlInterface <: AbstractScintillaControlInterface

end
function SCIUnpackNotifyMessage(self::ScintillaControlInterface, msg)::ScintillaNotification
format = "iiiiPiiiPPiiii"
bytes = GetBytes(win32ui, msg, calcsize(struct_, format))
position, ch, modifiers, modificationType, text_ptr, length, linesAdded, msg, wParam, lParam, line, foldLevelNow, foldLevelPrev, margin = unpack(struct_, format, bytes)
return ScintillaNotification(position, ch, modifiers, modificationType, text_ptr, length, linesAdded, msg, wParam, lParam, line, foldLevelNow, foldLevelPrev, margin)
end

function SCIAddText(self::ScintillaControlInterface, text)
SendMessage(self, scintillacon.SCI_ADDTEXT, encode(text, default_scintilla_encoding))
end

function SCIAddStyledText(self::ScintillaControlInterface, text, style = nothing)
if style != nothing
text = collect(map((char, style) -> char + Char(style), text))
text = join(text, "")
end
SendMessage(self, scintillacon.SCI_ADDSTYLEDTEXT, encode(text, default_scintilla_encoding))
end

function SCIInsertText(self::ScintillaControlInterface, text, pos = -1)
if isa(text, str)
text = encode(text, default_scintilla_encoding)
end
SendScintilla(self, scintillacon.SCI_INSERTTEXT, pos, text + null_byte)
end

function SCISetSavePoint(self::ScintillaControlInterface)
SendScintilla(self, scintillacon.SCI_SETSAVEPOINT)
end

function SCISetUndoCollection(self::ScintillaControlInterface, collectFlag)
SendScintilla(self, scintillacon.SCI_SETUNDOCOLLECTION, collectFlag)
end

function SCIBeginUndoAction(self::ScintillaControlInterface)
SendScintilla(self, scintillacon.SCI_BEGINUNDOACTION)
end

function SCIEndUndoAction(self::ScintillaControlInterface)
SendScintilla(self, scintillacon.SCI_ENDUNDOACTION)
end

function SCIGetCurrentPos(self::ScintillaControlInterface)
return SendScintilla(self, scintillacon.SCI_GETCURRENTPOS)
end

function SCIGetCharAt(self::ScintillaControlInterface, pos)
return Char(SendScintilla(self, scintillacon.SCI_GETCHARAT, pos) & 255)
end

function SCIGotoLine(self::ScintillaControlInterface, line)
SendScintilla(self, scintillacon.SCI_GOTOLINE, line)
end

function SCIBraceMatch(self::ScintillaControlInterface, pos, maxReStyle)
return SendScintilla(self, scintillacon.SCI_BRACEMATCH, pos, maxReStyle)
end

function SCIBraceHighlight(self::ScintillaControlInterface, pos, posOpposite)
return SendScintilla(self, scintillacon.SCI_BRACEHIGHLIGHT, pos, posOpposite)
end

function SCIBraceBadHighlight(self::ScintillaControlInterface, pos)
return SendScintilla(self, scintillacon.SCI_BRACEBADLIGHT, pos)
end

function SCIGetEndStyled(self::ScintillaControlInterface)
return SendScintilla(self, scintillacon.SCI_GETENDSTYLED)
end

function SCIStyleSetFore(self::ScintillaControlInterface, num, v)
return SendScintilla(self, scintillacon.SCI_STYLESETFORE, num, v)
end

function SCIStyleSetBack(self::ScintillaControlInterface, num, v)
return SendScintilla(self, scintillacon.SCI_STYLESETBACK, num, v)
end

function SCIStyleSetEOLFilled(self::ScintillaControlInterface, num, v)
return SendScintilla(self, scintillacon.SCI_STYLESETEOLFILLED, num, v)
end

function SCIStyleSetFont(self::ScintillaControlInterface, num, name, characterset = 0)
buff = encode(name + "\000", default_scintilla_encoding)
SendScintilla(self, scintillacon.SCI_STYLESETFONT, num, buff)
SendScintilla(self, scintillacon.SCI_STYLESETCHARACTERSET, num, characterset)
end

function SCIStyleSetBold(self::ScintillaControlInterface, num, bBold)
SendScintilla(self, scintillacon.SCI_STYLESETBOLD, num, bBold)
end

function SCIStyleSetItalic(self::ScintillaControlInterface, num, bItalic)
SendScintilla(self, scintillacon.SCI_STYLESETITALIC, num, bItalic)
end

function SCIStyleSetSize(self::ScintillaControlInterface, num, size)
SendScintilla(self, scintillacon.SCI_STYLESETSIZE, num, size)
end

function SCIGetViewWS(self::ScintillaControlInterface)
return SendScintilla(self, scintillacon.SCI_GETVIEWWS)
end

function SCISetViewWS(self::ScintillaControlInterface, val)
SendScintilla(self, scintillacon.SCI_SETVIEWWS, !(val == 0))
InvalidateRect(self)
end

function SCISetIndentationGuides(self::ScintillaControlInterface, val)
SendScintilla(self, scintillacon.SCI_SETINDENTATIONGUIDES, val)
end

function SCIGetIndentationGuides(self::ScintillaControlInterface)
return SendScintilla(self, scintillacon.SCI_GETINDENTATIONGUIDES)
end

function SCISetIndent(self::ScintillaControlInterface, val)
SendScintilla(self, scintillacon.SCI_SETINDENT, val)
end

function SCIGetIndent(self::ScintillaControlInterface, val)
return SendScintilla(self, scintillacon.SCI_GETINDENT)
end

function SCIGetViewEOL(self::ScintillaControlInterface)
return SendScintilla(self, scintillacon.SCI_GETVIEWEOL)
end

function SCISetViewEOL(self::ScintillaControlInterface, val)
SendScintilla(self, scintillacon.SCI_SETVIEWEOL, !(val == 0))
InvalidateRect(self)
end

function SCISetTabWidth(self::ScintillaControlInterface, width)
SendScintilla(self, scintillacon.SCI_SETTABWIDTH, width, 0)
end

function SCIStartStyling(self::ScintillaControlInterface, pos, mask)
SendScintilla(self, scintillacon.SCI_STARTSTYLING, pos, mask)
end

function SCISetStyling(self::ScintillaControlInterface, pos, attr)
SendScintilla(self, scintillacon.SCI_SETSTYLING, pos, attr)
end

function SCISetStylingEx(self::ScintillaControlInterface, ray)
address, length = buffer_info(ray)
SendScintilla(self, scintillacon.SCI_SETSTYLINGEX, length, address)
end

function SCIGetStyleAt(self::ScintillaControlInterface, pos)
return SendScintilla(self, scintillacon.SCI_GETSTYLEAT, pos)
end

function SCISetMarginWidth(self::ScintillaControlInterface, width)
SendScintilla(self, scintillacon.SCI_SETMARGINWIDTHN, 1, width)
end

function SCISetMarginWidthN(self::ScintillaControlInterface, n, width)
SendScintilla(self, scintillacon.SCI_SETMARGINWIDTHN, n, width)
end

function SCISetFoldFlags(self::ScintillaControlInterface, flags)
SendScintilla(self, scintillacon.SCI_SETFOLDFLAGS, flags)
end

function SCIMarkerDefineAll(self::ScintillaControlInterface, markerNum, markerType, fore, back)
SCIMarkerDefine(self, markerNum, markerType)
SCIMarkerSetFore(self, markerNum, fore)
SCIMarkerSetBack(self, markerNum, back)
end

function SCIMarkerDefine(self::ScintillaControlInterface, markerNum, markerType)
SendScintilla(self, scintillacon.SCI_MARKERDEFINE, markerNum, markerType)
end

function SCIMarkerSetFore(self::ScintillaControlInterface, markerNum, fore)
SendScintilla(self, scintillacon.SCI_MARKERSETFORE, markerNum, fore)
end

function SCIMarkerSetBack(self::ScintillaControlInterface, markerNum, back)
SendScintilla(self, scintillacon.SCI_MARKERSETBACK, markerNum, back)
end

function SCIMarkerAdd(self::ScintillaControlInterface, lineNo, markerNum)
SendScintilla(self, scintillacon.SCI_MARKERADD, lineNo, markerNum)
end

function SCIMarkerDelete(self::ScintillaControlInterface, lineNo, markerNum)
SendScintilla(self, scintillacon.SCI_MARKERDELETE, lineNo, markerNum)
end

function SCIMarkerDeleteAll(self::ScintillaControlInterface, markerNum = -1)
SendScintilla(self, scintillacon.SCI_MARKERDELETEALL, markerNum)
end

function SCIMarkerGet(self::ScintillaControlInterface, lineNo)
return SendScintilla(self, scintillacon.SCI_MARKERGET, lineNo)
end

function SCIMarkerNext(self::ScintillaControlInterface, lineNo, markerNum)
return SendScintilla(self, scintillacon.SCI_MARKERNEXT, lineNo, markerNum)
end

function SCICancel(self::ScintillaControlInterface)
SendScintilla(self, scintillacon.SCI_CANCEL)
end

function SCIAutoCShow(self::ScintillaControlInterface, text)
if type_(text) ∈ [type_([]), type_(())]
text = join(text, " ")
end
buff = encode(text + "\000", default_scintilla_encoding)
return SendScintilla(self, scintillacon.SCI_AUTOCSHOW, 0, buff)
end

function SCIAutoCCancel(self::ScintillaControlInterface)
SendScintilla(self, scintillacon.SCI_AUTOCCANCEL)
end

function SCIAutoCActive(self::ScintillaControlInterface)
return SendScintilla(self, scintillacon.SCI_AUTOCACTIVE)
end

function SCIAutoCComplete(self::ScintillaControlInterface)
return SendScintilla(self, scintillacon.SCI_AUTOCCOMPLETE)
end

function SCIAutoCStops(self::ScintillaControlInterface, stops)
buff = encode(stops + "\000", default_scintilla_encoding)
SendScintilla(self, scintillacon.SCI_AUTOCSTOPS, 0, buff)
end

function SCIAutoCSetAutoHide(self::ScintillaControlInterface, hide)
SendScintilla(self, scintillacon.SCI_AUTOCSETAUTOHIDE, hide)
end

function SCIAutoCSetFillups(self::ScintillaControlInterface, fillups)
SendScintilla(self, scintillacon.SCI_AUTOCSETFILLUPS, fillups)
end

function SCICallTipShow(self::ScintillaControlInterface, text, pos = -1)
if pos == -1
pos = GetSel(self)[1]
end
buff = encode(text + "\000", default_scintilla_encoding)
SendScintilla(self, scintillacon.SCI_CALLTIPSHOW, pos, buff)
end

function SCICallTipCancel(self::ScintillaControlInterface)
SendScintilla(self, scintillacon.SCI_CALLTIPCANCEL)
end

function SCICallTipActive(self::ScintillaControlInterface)
return SendScintilla(self, scintillacon.SCI_CALLTIPACTIVE)
end

function SCICallTipPosStart(self::ScintillaControlInterface)
return SendScintilla(self, scintillacon.SCI_CALLTIPPOSSTART)
end

function SCINewline(self::ScintillaControlInterface)
SendScintilla(self, scintillacon.SCI_NEWLINE)
end

function SCISetKeywords(self::ScintillaControlInterface, keywords, kw_list_no = 0)
buff = encode(keywords + "\000", default_scintilla_encoding)
SendScintilla(self, scintillacon.SCI_SETKEYWORDS, kw_list_no, buff)
end

function SCISetProperty(self::ScintillaControlInterface, name, value)
name_buff = array(array, "b", encode(name + "\000", default_scintilla_encoding))
val_buff = array(array, "b", encode(string(value) * "\000", default_scintilla_encoding))
address_name_buffer = buffer_info(name_buff)[1]
address_val_buffer = buffer_info(val_buff)[1]
SendScintilla(self, scintillacon.SCI_SETPROPERTY, address_name_buffer, address_val_buffer)
end

function SCISetStyleBits(self::ScintillaControlInterface, nbits)
SendScintilla(self, scintillacon.SCI_SETSTYLEBITS, nbits)
end

function SCIGetFoldLevel(self::ScintillaControlInterface, lineno)
return SendScintilla(self, scintillacon.SCI_GETFOLDLEVEL, lineno)
end

function SCIToggleFold(self::ScintillaControlInterface, lineno)
return SendScintilla(self, scintillacon.SCI_TOGGLEFOLD, lineno)
end

function SCIEnsureVisible(self::ScintillaControlInterface, lineno)
SendScintilla(self, scintillacon.SCI_ENSUREVISIBLE, lineno)
end

function SCIGetFoldExpanded(self::ScintillaControlInterface, lineno)
return SendScintilla(self, scintillacon.SCI_GETFOLDEXPANDED, lineno)
end

function SCISetEdgeColumn(self::ScintillaControlInterface, edge)
SendScintilla(self, scintillacon.SCI_SETEDGECOLUMN, edge)
end

function SCIGetEdgeColumn(self::ScintillaControlInterface)
return SendScintilla(self, scintillacon.SCI_GETEDGECOLUMN)
end

function SCISetEdgeMode(self::ScintillaControlInterface, mode)
SendScintilla(self, scintillacon.SCI_SETEDGEMODE, mode)
end

function SCIGetEdgeMode(self::ScintillaControlInterface)
return SendScintilla(self, scintillacon.SCI_GETEDGEMODE)
end

function SCISetEdgeColor(self::ScintillaControlInterface, color)
SendScintilla(self, scintillacon.SCI_SETEDGECOLOUR, color)
end

function SCIGetEdgeColor(self::ScintillaControlInterface)
return SendScintilla(self, scintillacon.SCI_GETEDGECOLOR)
end

function SCIGetDocPointer(self::ScintillaControlInterface)
return SendScintilla(self, scintillacon.SCI_GETDOCPOINTER)
end

function SCISetDocPointer(self::ScintillaControlInterface, p)
return SendScintilla(self, scintillacon.SCI_SETDOCPOINTER, 0, p)
end

function SCISetWrapMode(self::ScintillaControlInterface, mode)
return SendScintilla(self, scintillacon.SCI_SETWRAPMODE, mode)
end

function SCIGetWrapMode(self::ScintillaControlInterface)
return SendScintilla(self, scintillacon.SCI_GETWRAPMODE)
end

mutable struct CScintillaEditInterface <: AbstractCScintillaEditInterface
colorizer
end
function close(self::CScintillaEditInterface)
self.colorizer = nothing
end

function Clear(self::CScintillaEditInterface)
SendScintilla(self, win32con.WM_CLEAR)
end

function Clear(self::CScintillaEditInterface)
SendScintilla(self, win32con.WM_CLEAR)
end

function FindText(self::CScintillaEditInterface, flags, range, findText)
#= LPARAM for EM_FINDTEXTEX:
                typedef struct _findtextex {
                CHARRANGE chrg;
                LPCTSTR lpstrText;
                CHARRANGE chrgText;} FINDTEXTEX;
        typedef struct _charrange {
                LONG cpMin;
                LONG cpMax;} CHARRANGE;
         =#
findtextex_fmt = "llPll"
txt_buff = encode(findText + "\000", default_scintilla_encoding)
txt_array = array(array, "b", txt_buff)
ft_buff = pack(struct_, findtextex_fmt, range[1], range[2], buffer_info(txt_array)[1], 0, 0)
ft_array = array(array, "b", ft_buff)
rc = SendScintilla(self, EM_FINDTEXTEX, flags, buffer_info(ft_array)[1])
ftUnpacked = unpack(struct_, findtextex_fmt, ft_array)
return (rc, (ftUnpacked[4], ftUnpacked[5]))
end

function GetSel(self::CScintillaEditInterface)::Tuple
currentPos = SendScintilla(self, scintillacon.SCI_GETCURRENTPOS)
anchorPos = SendScintilla(self, scintillacon.SCI_GETANCHOR)
if currentPos < anchorPos
return (currentPos, anchorPos)
else
return (anchorPos, currentPos)
end
return currentPos
end

function GetSelText(self::CScintillaEditInterface)
start, end_ = GetSel(self)
txtBuf = array(array, "b", null_byte*((end_ - start) + 1))
addressTxtBuf = buffer_info(txtBuf)[1]
SendScintilla(self, EM_GETSELTEXT, 0, addressTxtBuf)
return decode(tobytes(txtBuf)[begin:-1], default_scintilla_encoding)
end

function SetSel(self::CScintillaEditInterface, start = 0, end_ = nothing)
if type_(start) == type_(())
@assert(end_ === nothing)
start, end_ = start
elseif end_ === nothing
end_ = start
end
if start < 0
start = GetTextLength(self)
end
if end_ < 0
end_ = GetTextLength(self)
end
@assert(start <= GetTextLength(self))
@assert(end_ <= GetTextLength(self))
cr = pack(struct_, "ll", start, end_)
crBuff = array(array, "b", cr)
addressCrBuff = buffer_info(crBuff)[1]
rc = SendScintilla(self, EM_EXSETSEL, 0, addressCrBuff)
end

function GetLineCount(self::CScintillaEditInterface)
return SendScintilla(self, win32con.EM_GETLINECOUNT)
end

function LineFromChar(self::CScintillaEditInterface, charPos = -1)
if charPos == -1
charPos = GetSel(self)[1]
end
@assert(charPos >= 0 && charPos <= GetTextLength(self))
return SendScintilla(self, EM_EXLINEFROMCHAR, 0, charPos)
end

function LineIndex(self::CScintillaEditInterface, line)
return SendScintilla(self, win32con.EM_LINEINDEX, line)
end

function ScrollCaret(self::CScintillaEditInterface)
return SendScintilla(self, win32con.EM_SCROLLCARET)
end

function GetCurLineNumber(self::CScintillaEditInterface)
return LineFromChar(self, SCIGetCurrentPos(self))
end

function GetTextLength(self::CScintillaEditInterface)
return SendScintilla(self, scintillacon.SCI_GETTEXTLENGTH)
end

function GetTextRange(self::CScintillaEditInterface, start = 0, end_ = -1, decode = true)
if end_ == -1
end_ = SendScintilla(self, scintillacon.SCI_GETTEXTLENGTH)
end
@assert(end_ >= start)
@assert(start >= 0 && start <= GetTextLength(self))
@assert(end_ >= 0 && end_ <= GetTextLength(self))
initer = null_byte*((end_ - start) + 1)
buff = array(array, "b", initer)
addressBuffer = buffer_info(buff)[1]
tr = pack(struct_, "llP", start, end_, addressBuffer)
trBuff = array(array, "b", tr)
addressTrBuff = buffer_info(trBuff)[1]
num_bytes = SendScintilla(self, EM_GETTEXTRANGE, 0, addressTrBuff)
ret = tobytes(buff)[begin:num_bytes]
if decode
ret = decode(ret, default_scintilla_encoding)
end
return ret
end

function ReplaceSel(self::CScintillaEditInterface, str)
buff = encode(str + "\000", default_scintilla_encoding)
SendScintilla(self, scintillacon.SCI_REPLACESEL, 0, buff)
end

function GetLine(self::CScintillaEditInterface, line = -1)
if line == -1
line = GetCurLineNumber(self)
end
start = LineIndex(self, line)
end_ = LineIndex(self, line + 1)
return GetTextRange(self, start, end_)
end

function SetReadOnly(self::CScintillaEditInterface, flag = 1)
return SendScintilla(self, win32con.EM_SETREADONLY, flag)
end

function LineScroll(self::CScintillaEditInterface, lines, cols = 0)
return SendScintilla(self, win32con.EM_LINESCROLL, cols, lines)
end

function GetFirstVisibleLine(self::CScintillaEditInterface)
return SendScintilla(self, win32con.EM_GETFIRSTVISIBLELINE)
end

function SetWordWrap(self::CScintillaEditInterface, mode)
if mode != win32ui.CRichEditView_WrapNone
throw(ValueError("We dont support word-wrap (I dont think :-)"))
end
end

mutable struct CScintillaColorEditInterface <: AbstractCScintillaColorEditInterface
colorizer
end
function _GetColorizer(self::CScintillaColorEditInterface)
if !hasfield(typeof(self), :colorizer)
self.colorizer = _MakeColorizer(self)
end
return self.colorizer
end

function _MakeColorizer(self::CScintillaColorEditInterface)
parent_func = (hasfield(typeof(GetParentFrame(self)), :_MakeColorizer) ? 
                getfield(GetParentFrame(self), :_MakeColorizer) : nothing)
if parent_func != nothing
return parent_func()
end
return BuiltinPythonSourceFormatter(formatter, self)
end

function Colorize(self::CScintillaColorEditInterface, start = 0, end_ = -1)
c = _GetColorizer(self)
if c != nothing
Colorize(c, start, end_)
end
end

function ApplyFormattingStyles(self::CScintillaColorEditInterface, bReload = 1)
c = _GetColorizer(self)
if c != nothing
ApplyFormattingStyles(c, bReload)
end
end

function HookFormatter(self::CScintillaColorEditInterface, parent = nothing)
c = _GetColorizer(self)
if c != nothing
HookFormatter(c, parent)
end
end

mutable struct CScintillaEdit <: window.Wnd
wnd

            CScintillaEdit(wnd = nothing) = begin
                if wnd === nothing
wnd = win32ui.CreateWnd()
end
window.Wnd.__init__(self, wnd)
                new(wnd )
            end
end
function SendScintilla(self::CScintillaEdit, msg, w = 0, l = 0)
return SendMessage(self, msg, w, l)
end

function CreateWindow(self::CScintillaEdit, style, rect, parent, id)
CreateWindow(self._obj_, "Scintilla", "Scintilla", style, rect)
end
