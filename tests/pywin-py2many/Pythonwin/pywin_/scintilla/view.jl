using Printf
using PyCall
pythoncom = pyimport("pythoncom")
win32ui = pyimport("win32ui")
include("formatter.jl")
using win32com_.gen_py.framework.editor: GetEditorOption
include("find.jl")
import win32com_.gen_py.framework.scriptutils

using win32com_.gen_py.framework: interact
using config: ConfigManager
include("control.jl")
include("IDLEenvironment.jl")
using win32com_.gen_py.mfc: docview
using win32com_.gen_py.mfc: dialog
include("scintillacon.jl")
import win32con

import afxres
import string



import __main__
include("bindings.jl")
include("keycodes.jl")



PRINTDLGORD = 1538
IDC_PRINT_MAG_EDIT = 1010
EM_FORMATRANGE = win32con.WM_USER + 57
abstract type AbstractCScintillaView <: Abstractdocview.CtrlView end
wordbreaks = (("._" + string.ascii_uppercase) + string.ascii_lowercase) + string.digits
patImport = compile(re, "import (?P<name>.*)")
_event_commands = ["win32ui.ID_FILE_LOCATE", "win32ui.ID_FILE_CHECK", "afxres.ID_FILE_CLOSE", "afxres.ID_FILE_NEW", "afxres.ID_FILE_OPEN", "afxres.ID_FILE_SAVE", "afxres.ID_FILE_SAVE_AS", "win32ui.ID_FILE_SAVE_ALL", "afxres.ID_EDIT_UNDO", "afxres.ID_EDIT_REDO", "afxres.ID_EDIT_CUT", "afxres.ID_EDIT_COPY", "afxres.ID_EDIT_PASTE", "afxres.ID_EDIT_SELECT_ALL", "afxres.ID_EDIT_FIND", "afxres.ID_EDIT_REPEAT", "afxres.ID_EDIT_REPLACE", "win32ui.ID_VIEW_WHITESPACE", "win32ui.ID_VIEW_FIXED_FONT", "win32ui.ID_VIEW_BROWSE", "win32ui.ID_VIEW_INTERACTIVE", "afxres.ID_WINDOW_ARRANGE", "afxres.ID_WINDOW_CASCADE", "afxres.ID_WINDOW_NEW", "afxres.ID_WINDOW_SPLIT", "afxres.ID_WINDOW_TILE_HORZ", "afxres.ID_WINDOW_TILE_VERT", "afxres.ID_APP_EXIT", "afxres.ID_APP_ABOUT"]
_extra_event_commands = [("EditDelete", afxres.ID_EDIT_CLEAR), ("LocateModule", win32ui.ID_FILE_LOCATE), ("GotoLine", win32ui.ID_EDIT_GOTO_LINE), ("DbgBreakpointToggle", win32ui.IDC_DBG_ADD), ("DbgGo", win32ui.IDC_DBG_GO), ("DbgStepOver", win32ui.IDC_DBG_STEPOVER), ("DbgStep", win32ui.IDC_DBG_STEP), ("DbgStepOut", win32ui.IDC_DBG_STEPOUT), ("DbgBreakpointClearAll", win32ui.IDC_DBG_CLEAR), ("DbgClose", win32ui.IDC_DBG_CLOSE)]
event_commands = []
function _CreateEvents()
for name in _event_commands
val = eval(name)
name_parts = split(name, "_")[2:end]
name_parts = [capitalize(p) for p in name_parts]
event = join(name_parts, "")
push!(event_commands, (event, val))
end
for (name, id) in _extra_event_commands
push!(event_commands, (name, id))
end
end

_CreateEvents()
empty!(_event_commands)
empty!(_extra_event_commands)
command_reflectors = [(win32ui.ID_EDIT_UNDO, win32con.WM_UNDO), (win32ui.ID_EDIT_REDO, scintillacon.SCI_REDO), (win32ui.ID_EDIT_CUT, win32con.WM_CUT), (win32ui.ID_EDIT_COPY, win32con.WM_COPY), (win32ui.ID_EDIT_PASTE, win32con.WM_PASTE), (win32ui.ID_EDIT_CLEAR, win32con.WM_CLEAR), (win32ui.ID_EDIT_SELECT_ALL, scintillacon.SCI_SELECTALL)]
function DoBraceMatch(control)
curPos = SCIGetCurrentPos(control)
charBefore = " "
if curPos
charBefore = SCIGetCharAt(control, curPos - 1)
end
charAt = SCIGetCharAt(control, curPos)
braceAtPos = -1
braceOpposite = -1
if findfirst(charBefore, "[](){}") != Nothing
braceAtPos = curPos - 1
end
if braceAtPos == -1
if charAt ∈ "[](){}"
braceAtPos = curPos
end
end
if braceAtPos != -1
braceOpposite = SCIBraceMatch(control, braceAtPos, 0)
end
if braceAtPos != -1 && braceOpposite == -1
SCIBraceBadHighlight(control, braceAtPos)
else
SCIBraceHighlight(control, braceAtPos, braceOpposite)
end
end

function _get_class_attributes(ob)::Vector
items = []
try
items = items + dir(ob)
for i in ob.__bases__
for item in _get_class_attributes(i)
if item ∉ items
push!(items, item)
end
end
end
catch exn
if exn isa AttributeError
#= pass =#
end
end
return items
end

mutable struct CScintillaView <: docview.CtrlView
_tabWidth::Int64
bAutoCompleteAttributes::Int64
bShowCallTips::Int64
bMatchBraces::Int64
bindings
idle
SendScintilla
starts
OnCmdViewWS
OnUpdateViewWS
OnCmdViewIndentationGuides
OnUpdateViewIndentationGuides
OnCmdViewRightEdge
OnUpdateViewRightEdge
OnCmdViewEOL
OnUpdateViewEOL
OnCmdViewFixedFont
OnUpdateViewFixedFont
OnCmdFileLocate
OnCmdEditFind
OnCmdEditRepeat
OnCmdEditReplace
OnCmdGotoLine
OnFilePrint
OnFilePrintPreview
OnKeyDown

            CScintillaView(doc) = begin
                docview.CtrlView.__init__(self, doc, "Scintilla", (((win32con.WS_CHILD | win32con.WS_VSCROLL) | win32con.WS_HSCROLL) | win32con.WS_CLIPCHILDREN) | win32con.WS_VISIBLE)
idle.IDLEExtension("AutoExpand")
                new(doc)
            end
end
function OnDestroy(self::CScintillaView, msg)
self.SendScintilla = nothing
return OnDestroy(docview.CtrlView, self)
end

function _MakeColorizer(self::CScintillaView)
ext = splitext(os.path, GetPathName(GetDocument(self)))[2]
return BuiltinPythonSourceFormatter(formatter, self, ext)
end

function SCISetTabWidth(self::CScintillaView, width)
self._tabWidth = width
SCISetTabWidth(control.CScintillaEditInterface, self)
end

function GetTabWidth(self::CScintillaView)::Int64
return self._tabWidth
end

function HookHandlers(self::CScintillaView)
for (name, val) in event_commands
bind(self.bindings, name, nothing, val)
end
for (command, reflection) in command_reflectors
handler = (id, code, ss, tosend) -> ss(tosend) && 0
HookCommand(self, handler, command)
end
HookCommand(self, self.OnCmdViewWS, win32ui.ID_VIEW_WHITESPACE)
HookCommandUpdate(self, self.OnUpdateViewWS, win32ui.ID_VIEW_WHITESPACE)
HookCommand(self, self.OnCmdViewIndentationGuides, win32ui.ID_VIEW_INDENTATIONGUIDES)
HookCommandUpdate(self, self.OnUpdateViewIndentationGuides, win32ui.ID_VIEW_INDENTATIONGUIDES)
HookCommand(self, self.OnCmdViewRightEdge, win32ui.ID_VIEW_RIGHT_EDGE)
HookCommandUpdate(self, self.OnUpdateViewRightEdge, win32ui.ID_VIEW_RIGHT_EDGE)
HookCommand(self, self.OnCmdViewEOL, win32ui.ID_VIEW_EOL)
HookCommandUpdate(self, self.OnUpdateViewEOL, win32ui.ID_VIEW_EOL)
HookCommand(self, self.OnCmdViewFixedFont, win32ui.ID_VIEW_FIXED_FONT)
HookCommandUpdate(self, self.OnUpdateViewFixedFont, win32ui.ID_VIEW_FIXED_FONT)
HookCommand(self, self.OnCmdFileLocate, win32ui.ID_FILE_LOCATE)
HookCommand(self, self.OnCmdEditFind, win32ui.ID_EDIT_FIND)
HookCommand(self, self.OnCmdEditRepeat, win32ui.ID_EDIT_REPEAT)
HookCommand(self, self.OnCmdEditReplace, win32ui.ID_EDIT_REPLACE)
HookCommand(self, self.OnCmdGotoLine, win32ui.ID_EDIT_GOTO_LINE)
HookCommand(self, self.OnFilePrint, afxres.ID_FILE_PRINT)
HookCommand(self, self.OnFilePrint, afxres.ID_FILE_PRINT_DIRECT)
HookCommand(self, self.OnFilePrintPreview, win32ui.ID_FILE_PRINT_PREVIEW)
HookMessage(self, self.OnKeyDown, win32con.WM_KEYDOWN)
HookMessage(self, self.OnKeyDown, win32con.WM_SYSKEYDOWN)
HookFormatter(self)
end

function OnInitialUpdate(self::CScintillaView)
doc = GetDocument(self)
SendScintilla(self, scintillacon.SCI_SETCODEPAGE, scintillacon.SC_CP_UTF8, 0)
SendScintilla(self, scintillacon.SCI_SETKEYSUNICODE, 1, 0)
SendScintilla(self, scintillacon.SCI_SETMARGINTYPEN, 1, scintillacon.SC_MARGIN_SYMBOL)
SendScintilla(self, scintillacon.SCI_SETMARGINMASKN, 1, 15)
SendScintilla(self, scintillacon.SCI_SETMARGINTYPEN, 2, scintillacon.SC_MARGIN_SYMBOL)
SendScintilla(self, scintillacon.SCI_SETMARGINMASKN, 2, scintillacon.SC_MASK_FOLDERS)
SendScintilla(self, scintillacon.SCI_SETMARGINSENSITIVEN, 2, 1)
HookViewNotifications(GetDocument(self), self)
HookHandlers(self)
OnWinIniChange(self, nothing)
SetSel(self)
FinalizeViewCreation(GetDocument(self), self)
end

function _GetSubConfigNames(self::CScintillaView)
return nothing
end

function OnWinIniChange(self::CScintillaView, section = nothing)
prepare_configure(self.bindings)
try
DoConfigChange(self)
finally
complete_configure(self.bindings)
end
end

function DoConfigChange(self::CScintillaView)
self.bAutoCompleteAttributes = GetEditorOption("Autocomplete Attributes", 1)
self.bShowCallTips = GetEditorOption("Show Call Tips", 1)
configure(configManager, self, _GetSubConfigNames(self))
if configManager.last_error
MessageBox(win32ui, configManager.last_error, "Configuration Error")
end
self.bMatchBraces = GetEditorOption("Match Braces", 1)
ApplyFormattingStyles(self, 1)
end

function OnDestroy(self::CScintillaView, msg)
close(self.bindings)
self.bindings = nothing
close(self.idle)
self.idle = nothing
close(control.CScintillaColorEditInterface, self)
return OnDestroy(docview.CtrlView, self)
end

function OnMouseWheel(self::CScintillaView, msg)
zDelta = msg[3] >> 16
vpos = GetScrollPos(self, win32con.SB_VERT)
vpos = vpos - (zDelta / 40)
SetScrollPos(self, win32con.SB_VERT, vpos)
SendScintilla(self, win32con.WM_VSCROLL, (vpos << 16) | win32con.SB_THUMBPOSITION, 0)
end

function OnBraceMatch(self::CScintillaView, std, extra)
if !(self.bMatchBraces) != 0
return
end
DoBraceMatch(self)
end

function OnNeedShown(self::CScintillaView, std, extra)
notify = SCIUnpackNotifyMessage(self, extra)
EnsureCharsVisible(self, notify.position)
end

function EnsureCharsVisible(self::CScintillaView, start, end_ = nothing)
if end_ === nothing
end_ = start
end
lineStart = LineFromChar(self, min(start, end_))
lineEnd = LineFromChar(self, max(start, end_))
while lineStart <= lineEnd
SCIEnsureVisible(self, lineStart)
lineStart = lineStart + 1
end
end

function AppendMenu(self::CScintillaView, menu, text = "", event = nothing, flags = nothing, checked = 0)
if event === nothing
@assert(flags != nothing)
cmdid = 0
else
cmdid = get_command_id(self.bindings, event)
if cmdid === nothing
@printf("View.AppendMenu(): Unknown event \"%s\" specified for menu text \"%s\" - ignored\n", event, text)
return
end
keyname = get_key_binding(configManager, event, _GetSubConfigNames(self))
if keyname != nothing
text = text * "\t" + keyname
end
end
if flags === nothing
flags = win32con.MF_STRING | win32con.MF_ENABLED
end
if checked
flags = flags | win32con.MF_CHECKED
end
AppendMenu(menu, flags, cmdid, text)
end

function OnKeyDown(self::CScintillaView, msg)
return fire_key_event(self.bindings, msg)
end

function GotoEndOfFileEvent(self::CScintillaView, event)
SetSel(self, -1)
end

function KeyDotEvent(self::CScintillaView, event)::Int64
s, e = GetSel(self)
if s != e
return 1
end
SCIAddText(self, ".")
if self.bAutoCompleteAttributes != 0
_AutoComplete(self)
end
end

function OnCmdViewWS(self::CScintillaView, cmd, code)
viewWS = SCIGetViewWS(self)
SCISetViewWS(self, !(viewWS))
end

function OnUpdateViewWS(self::CScintillaView, cmdui)
SetCheck(cmdui, SCIGetViewWS(self))
Enable(cmdui)
end

function OnCmdViewIndentationGuides(self::CScintillaView, cmd, code)
viewIG = SCIGetIndentationGuides(self)
SCISetIndentationGuides(self, !(viewIG))
end

function OnUpdateViewIndentationGuides(self::CScintillaView, cmdui)
SetCheck(cmdui, SCIGetIndentationGuides(self))
Enable(cmdui)
end

function OnCmdViewRightEdge(self::CScintillaView, cmd, code)
if SCIGetEdgeMode(self) == scintillacon.EDGE_NONE
mode = scintillacon.EDGE_BACKGROUND
else
mode = scintillacon.EDGE_NONE
end
SCISetEdgeMode(self, mode)
end

function OnUpdateViewRightEdge(self::CScintillaView, cmdui)
SetCheck(cmdui, SCIGetEdgeMode(self) != scintillacon.EDGE_NONE)
Enable(cmdui)
end

function OnCmdViewEOL(self::CScintillaView, cmd, code)
viewEOL = SCIGetViewEOL(self)
SCISetViewEOL(self, !(viewEOL))
end

function OnUpdateViewEOL(self::CScintillaView, cmdui)
SetCheck(cmdui, SCIGetViewEOL(self))
Enable(cmdui)
end

function OnCmdViewFixedFont(self::CScintillaView, cmd, code)
_GetColorizer(self).bUseFixed = !(_GetColorizer(self).bUseFixed)
ApplyFormattingStyles(self, 0)
ScrollCaret(self)
end

function OnUpdateViewFixedFont(self::CScintillaView, cmdui)
c = _GetColorizer(self)
if c != nothing
SetCheck(cmdui, c.bUseFixed)
end
Enable(cmdui, c != nothing)
end

function OnCmdEditFind(self::CScintillaView, cmd, code)
ShowFindDialog(find)
end

function OnCmdEditRepeat(self::CScintillaView, cmd, code)
FindNext(find)
end

function OnCmdEditReplace(self::CScintillaView, cmd, code)
ShowReplaceDialog(find)
end

function OnCmdFileLocate(self::CScintillaView, cmd, id)::Int64
line = strip(GetLine(self))
m = match(patImport, line)
if m
modName = group(m, "name")
fileName = LocatePythonFile(win32com_.gen_py.framework.scriptutils, modName)
if fileName === nothing
SetStatusText(win32ui, "Can\'t locate module %s" % modName)
return 1
else
OpenDocumentFile(GetApp(win32ui), fileName)
end
else
return 1
end
return 0
end

function OnCmdGotoLine(self::CScintillaView, cmd, id)::Int64
try
lineNo = parse(Int, input("Enter Line Number")) - 1
catch exn
if exn isa (ValueError, KeyboardInterrupt)
return 0
end
end
SCIEnsureVisible(self, lineNo)
SCIGotoLine(self, lineNo)
return 0
end

function SaveTextFile(self::CScintillaView, filename, encoding = nothing)::Int64
doc = GetDocument(self)
_SaveTextToFile(doc, self, filename, encoding)
SetModifiedFlag(doc, 0)
return 1
end

function _AutoComplete(self::CScintillaView)
function list2dict(l)::Dict
ret = Dict()
for i in l
ret[i] = nothing
end
return ret
end

SCIAutoCCancel(self)
ob = _GetObjectAtPos(self)
if ob === nothing
ob = _GetObjectAtPos(self)
end
items_dict = Dict()
if ob != nothing
try
if hasfield(typeof(ob), :_obj_)
try
update(items_dict, list2dict(dir(ob._obj_)))
catch exn
if exn isa AttributeError
#= pass =#
end
end
end
try
update(items_dict, list2dict(dir(ob)))
catch exn
if exn isa AttributeError
#= pass =#
end
end
if hasfield(typeof(ob), :__class__)
update(items_dict, list2dict(_get_class_attributes(ob.__class__)))
end
try
update(items_dict, ob.__class__._prop_map_get_)
update(items_dict, ob.__class__._prop_map_put_)
catch exn
if exn isa AttributeError
#= pass =#
end
end
if hasfield(typeof(ob), :_oleobj_)
try
for iTI in 0:GetTypeInfoCount(ob._oleobj_) - 1
typeInfo = GetTypeInfo(ob._oleobj_, iTI)
_UpdateWithITypeInfo(self, items_dict, typeInfo)
end
catch exn
#= pass =#
end
end
catch exn
SetStatusText(win32ui, "Error attempting to get object attributes - %s" % (repr(exc_info(sys)[1]),))
end
end
items = [string(k) for k in keys(items_dict)]
items = [k for k in items if !startswith(k, "_") ]
if !(items)
left, right = _GetWordSplit(self)
if left == ""
return nothing
end
minline, maxline, curclass = _GetClassInfoFromBrowser(self)
endpos = LineIndex(self, maxline)
text = GetTextRange(self, LineIndex(self, minline), endpos)
try
l = collect(eachmatch(Regex(("\\b" + left) * "\\.\\w+"), text))
catch exn
if exn isa re.error
l = []
end
end
prefix = length(left) + 1
unique = Dict()
for li in l
unique[li[prefix + 1:end]] = 1
end
if curclass && left == "self"
_UpdateWithClassMethods(self, unique, curclass)
end
items = [word for word in keys(unique) if word[begin:2] != "__" || word[length(word) - -1:end] != "__" ]
try
remove(items, right[2:end])
catch exn
if exn isa ValueError
#= pass =#
end
end
end
if items
sort(items)
SCIAutoCSetAutoHide(self, 0)
SCIAutoCShow(self, items)
end
end

function _UpdateWithITypeInfo(self::CScintillaView, items_dict, typeInfo)
typeInfos = [typeInfo]
inspectedIIDs = Dict(pythoncom.IID_IDispatch => nothing)
while length(typeInfos) > 0
typeInfo = pop(typeInfos)
typeAttr = GetTypeAttr(typeInfo)
if typeAttr.iid ∉ inspectedIIDs
inspectedIIDs[typeAttr.iid] = nothing
for iFun in 0:typeAttr.cFuncs - 1
funDesc = GetFuncDesc(typeInfo, iFun)
funName = GetNames(typeInfo, funDesc.memid)[1]
if funName ∉ items_dict
items_dict[funName + 1] = nothing
end
end
for iImplType in 0:typeAttr.cImplTypes - 1
iRefType = GetRefTypeOfImplType(typeInfo, iImplType)
refTypeInfo = GetRefTypeInfo(typeInfo, iRefType)
push!(typeInfos, refTypeInfo)
end
end
end
end

function _UpdateWithClassMethods(self::CScintillaView, dict, classinfo)
if !hasfield(typeof(classinfo), :methods)
return
end
update(dict, classinfo.methods)
for super in classinfo.super
if hasfield(typeof(super), :methods)
_UpdateWithClassMethods(self, dict, super)
end
end
end

function _GetClassInfoFromBrowser(self::CScintillaView, pos = -1)
minline = 0
maxline = GetLineCount(self) - 1
doc = GetActiveDocument(GetParentFrame(self))
browser = nothing
try
if doc != nothing
browser = GetAllViews(doc)[2]
end
catch exn
if exn isa IndexError
#= pass =#
end
end
if browser === nothing
return (minline, maxline, nothing)
end
if !(collect(browser))
return (minline, maxline, nothing)
end
path = GetPathName(GetDocument(self))
if !(path)
return (minline, maxline, nothing)
end
curmodule, path = GetPackageModuleName(win32com_.gen_py.framework.scriptutils, path)
try
clbrdata = collect(browser).root.clbrdata
catch exn
if exn isa AttributeError
return (minline, maxline, nothing)
end
end
curline = LineFromChar(self, pos)
curclass = nothing
for item in values(clbrdata)
if item.module === curmodule
item_lineno = item.lineno - 1
if minline < item_lineno <= curline
minline = item_lineno
curclass = item
end
if curline < item_lineno < maxline
maxline = item_lineno
end
end
end
return (minline, maxline, curclass)
end

function _GetObjectAtPos(self::CScintillaView, pos = -1, bAllowCalls = 0)
left, right = _GetWordSplit(self, pos, bAllowCalls)
if left
namespace = copy(sys.modules)
update(namespace, __main__.__dict__)
try
if interact.edit != nothing && interact.edit.currentView != nothing
globs, locs = GetContext(interact.edit.currentView)[begin:2]
if globs
update(namespace, globs)
end
if locs
update(namespace, locs)
end
end
catch exn
if exn isa ImportError
#= pass =#
end
end
try
return eval(left, namespace)
catch exn
#= pass =#
end
end
return nothing
end

function _GetWordSplit(self::CScintillaView, pos = -1, bAllowCalls = 0)::Tuple
if pos == -1
pos = GetSel(self)[1] - 1
end
limit = GetTextLength(self)
before = []
after = []
index = pos - 1
wordbreaks_use = wordbreaks
if bAllowCalls
wordbreaks_use = wordbreaks_use * "()[]"
end
while index >= 0
char = SCIGetCharAt(self, index)
if char ∉ wordbreaks_use
has_break = true
break;
end
insert(before, 0, char)
index = index - 1
end
index = pos
while index <= limit
char = SCIGetCharAt(self, index)
if char ∉ wordbreaks_use
has_break = true
break;
end
push!(after, char)
index = index + 1
end
return (join(before, ""), join(after, ""))
end

function OnPrepareDC(self::CScintillaView, dc, pInfo)
if IsPrinting(dc)
if !GetPreview(pInfo) && self.starts != nothing
prevPage = GetCurPage(pInfo) - 1
if prevPage > 0 && self.starts[prevPage + 1] >= GetTextLength(self)
SetContinuePrinting(pInfo, 0)
return
end
end
SetMapMode(dc, win32con.MM_TEXT)
end
end

function OnPreparePrinting(self::CScintillaView, pInfo)
flags = (win32ui.PD_USEDEVMODECOPIES | win32ui.PD_ALLPAGES) | win32ui.PD_NOSELECTION
SetMinPage(pInfo, 1)
SetFromPage(pInfo, 1)
SetToPage(pInfo, 1)
ret = DoPreparePrinting(self, pInfo)
return ret
end

function OnBeginPrinting(self::CScintillaView, dc, pInfo)
self.starts = nothing
return OnBeginPrinting(self._obj_, dc, pInfo)
end

function CalculatePageRanges(self::CScintillaView, dc, pInfo)
self.starts = Dict(0 => 0)
metrics = GetTextMetrics(dc)
left, top, right, bottom = GetDraw(pInfo)
rc = (left, top + Int(floor(9*metrics["tmHeight"] / 2)), right, bottom)
pageStart = 0
maxPage = 0
textLen = GetTextLength(self)
while pageStart < textLen
pageStart = FormatRange(self, dc, pageStart, textLen, rc, 0)
maxPage = maxPage + 1
self.starts[maxPage + 1] = pageStart
end
self.starts[maxPage + 2] = textLen
SetMaxPage(pInfo, maxPage)
end

function OnFilePrintPreview(self::CScintillaView)
OnFilePrintPreview(self._obj_)
end

function OnFilePrint(self::CScintillaView)
OnFilePrint(self._obj_)
end

function FormatRange(self::CScintillaView, dc, pageStart, lengthDoc, rc, draw)
#= 
        typedef struct _formatrange {
                HDC hdc;
                HDC hdcTarget;
                RECT rc;
                RECT rcPage;
                CHARRANGE chrg;} FORMATRANGE;
         =#
fmt = "PPIIIIIIIIll"
hdcRender = GetHandleOutput(dc)
hdcFormat = GetHandleAttrib(dc)
fr = pack(struct_, fmt, hdcRender, hdcFormat, rc[1], rc[2], rc[3], rc[4], rc[1], rc[2], rc[3], rc[4], pageStart, lengthDoc)
nextPageStart = SendScintilla(self, EM_FORMATRANGE, draw, fr)
return nextPageStart
end

function OnPrint(self::CScintillaView, dc, pInfo)
metrics = GetTextMetrics(dc)
if self.starts === nothing
CalculatePageRanges(self, dc, pInfo)
end
pageNum = GetCurPage(pInfo) - 1
doc = GetDocument(self)
cxChar = metrics["tmAveCharWidth"]
cyChar = metrics["tmHeight"]
left, top, right, bottom = GetDraw(pInfo)
TextOut(dc, 0, 2*cyChar, GetTitle(doc))
pagenum_str = LoadString(win32ui, afxres.AFX_IDS_PRINTPAGENUM) % (pageNum + 1,)
SetTextAlign(dc, win32con.TA_RIGHT)
TextOut(dc, right, 2*cyChar, pagenum_str)
SetTextAlign(dc, win32con.TA_LEFT)
top = top + Int(floor(7*cyChar / 2))
MoveTo(dc, left, top)
LineTo(dc, right, top)
top = top + cyChar
rc = (left, top, right, bottom)
nextPageStart = FormatRange(self, dc, self.starts[pageNum + 1], self.starts[pageNum + 2], rc, 1)
end

function LoadConfiguration()
global configManager
configName = GetProfileVal(win32ui, "Editor", "Keyboard Config", "default")
rc = GetProfileVal(win32ui, "Editor", "Keyboard Config", "default")
configManager = ConfigManager(configName)
if configManager.last_error
bTryDefault = 0
msg = "Error loading configuration \'%s\'\n\n%s" % (configName, configManager.last_error)
if configName != "default"
msg = msg * "\n\nThe default configuration will be loaded."
bTryDefault = 1
end
MessageBox(win32ui, msg)
if bTryDefault != 0
configManager = ConfigManager("default")
if configManager.last_error
MessageBox(win32ui, "Error loading configuration \'default\'\n\n%s" % configManager.last_error)
end
end
end
end

configManager = nothing
LoadConfiguration()