using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
import linecache
import win32com_.gen_py.framework.scriptutils


import win32con
import regex

import string


using win32com_.gen_py.mfc: docview, dialog, afxres
using win32com_.gen_py.framework.editor: GetEditorOption, SetEditorOption, GetEditorFontOption, SetEditorFontOption, defaultCharacterFormat
patImport = symcomp(regex, "import \\(<name>.*\\)")
patIndent = compile(regex, "^\\([ \t]*[~ \t]\\)")
ID_LOCATE_FILE = 57856
abstract type AbstractEditorDocument <: AbstractParentEditorDocument end
abstract type AbstractEditorView <: AbstractParentEditorView end
abstract type AbstractEditorTemplate <: AbstractEditorTemplateBase end
ID_GOTO_LINE = 925697
MSG_CHECK_EXTERNAL_FILE = win32con.WM_USER + 1999
MODIFYING_VK_KEYS = [win32con.VK_BACK, win32con.VK_TAB, win32con.VK_RETURN, win32con.VK_SPACE, win32con.VK_DELETE]
for k in 48:90
push!(MODIFYING_VK_KEYS, k)
end
MODIFYING_VK_KEYS_CTRL = [win32con.VK_BACK, win32con.VK_RETURN, win32con.VK_SPACE, win32con.VK_DELETE]
MODIFYING_VK_KEYS_ALT = [win32con.VK_BACK, win32con.VK_RETURN, win32con.VK_SPACE, win32con.VK_DELETE]
isRichText = 1
using document: EditorDocumentBase
ParentEditorDocument = EditorDocumentBase
mutable struct EditorDocument <: AbstractEditorDocument

end
function OnOpenDocument(self::EditorDocument, filename)::Int64
SetPathName(self, filename)
BeginWaitCursor(self)
SetStatusText(win32ui, "Loading file...", 1)
try
f = readline(filename)
catch exn
if exn isa IOError
MessageBox(win32ui, filename + "\nCan not find this file\nPlease verify that the correct path and file name are given")
EndWaitCursor(self)
return 0
end
end
raw = read(f)
close(f)
contents = TranslateLoadedData(self, raw)
rc = 0
if IsWin32s(win32ui) && length(contents) > 62000
MessageBox(win32ui, "This file is too big for Python on Windows 3.1\r\nPlease use another editor to view this file.")
else
try
SetWindowText(GetFirstView(self), contents)
rc = 1
catch exn
if exn isa TypeError
MessageBox(win32ui, "This file contains NULL bytes, and can not be edited")
rc = 0
end
end
EndWaitCursor(self)
SetModifiedFlag(self, 0)
_DocumentStateChanged(self)
end
return rc
end

function TranslateLoadedData(self::EditorDocument, data)
#= Given raw data read from a file, massage it suitable for the edit window =#
if find(data[begin:250], "\r") == -1
SetStatusText(win32ui, "Translating from Unix file format - please wait...", 1)
return replace(data, Regex("\r*\n") => s"\r\n")
else
return data
end
end

function SaveFile(self::EditorDocument, fileName, encoding = nothing)
if isRichText != 0
view = GetFirstView(self)
SaveTextFile(view, fileName, encoding)
else
SaveFile(GetFirstView(self), fileName)
end
try
checkcache(linecache)
catch exn
#= pass =#
end
end

function SetAllLineColors(self::EditorDocument, color = nothing)
for view in GetAllViews(self)
SetAllLineColors(view, color)
end
end

function SetLineColor(self::EditorDocument, lineNo, color)
#= Color a line of all views =#
for view in GetAllViews(self)
SetLineColor(view, lineNo, color)
end
end

ParentEditorView = docview.RichEditView
mutable struct EditorView <: AbstractEditorView
addToMRU::Int64
bCheckingFile::Int64
defCharFormat
bSmartTabs
tabSize
indentSize
bUseTabs
OnCheckExternalDocumentUpdated
OnRClick
OnSetFocus
OnKeyDown
OnKeyCtrlY
OnKeyCtrlG
OnKeyTab
OnKeyEnter
OnCmdLocateFile
OnCmdGotoLine
OnEditPaste
OnEditCut
_obj_

            EditorView(doc) = begin
                ParentEditorView.__init__(self, doc)
if isRichText
SetWordWrap(win32ui.CRichEditView_WrapNone)
end
HookHandlers()
                new(doc)
            end
end
function OnInitialUpdate(self::EditorView)
rc = OnInitialUpdate(self._obj_)
SetDefaultCharFormat(self, self.defCharFormat)
return rc
end

function CutCurLine(self::EditorView)
curLine = LineFromChar(self._obj_)
nextLine = curLine + 1
start = LineIndex(self._obj_, curLine)
end_ = LineIndex(self._obj_, nextLine)
if end_ == 0
end_ = start + GetLineLength(self.end, curLine)
end
SetSel(self._obj_, start, end_)
Cut(self._obj_)
end

function _PrepareUserStateChange(self::EditorView)::Tuple
#= Return selection, lineindex, etc info, so it can be restored =#
SetRedraw(self, 0)
return (GetModify(self), GetSel(self), GetFirstVisibleLine(self))
end

function _EndUserStateChange(self::EditorView, info)
scrollOff = info[3] - GetFirstVisibleLine(self)
if scrollOff
LineScroll(self, scrollOff)
end
SetSel(self, info[2])
SetModify(self, info[1])
SetRedraw(self, 1)
InvalidateRect(self)
UpdateWindow(self)
end

function _UpdateUIForState(self::EditorView)
SetReadOnly(self, _IsReadOnly(GetDocument(self)))
end

function SetAllLineColors(self::EditorView, color = nothing)
if isRichText != 0
info = _PrepareUserStateChange(self)
try
if color === nothing
color = self.defCharFormat[5]
end
SetSel(self, 0, -1)
SetSelectionCharFormat(self, (win32con.CFM_COLOR, 0, 0, 0, color))
finally
_EndUserStateChange(self, info)
end
end
end

function SetLineColor(self::EditorView, lineNo, color)
#= lineNo is the 1 based line number to set.  If color is None, default color is used. =#
if isRichText != 0
info = _PrepareUserStateChange(self)
try
if color === nothing
color = self.defCharFormat[5]
end
lineNo = lineNo - 1
startIndex = LineIndex(self, lineNo)
if startIndex != -1
SetSel(self, startIndex, LineIndex(self, lineNo + 1))
SetSelectionCharFormat(self, (win32con.CFM_COLOR, 0, 0, 0, color))
end
finally
_EndUserStateChange(self, info)
end
end
end

function Indent(self::EditorView)
#= Insert an indent to move the cursor to the next tab position.

        Honors the tab size and 'use tabs' settings.  Assumes the cursor is already at the
        position to be indented, and the selection is a single character (ie, not a block)
         =#
start, end_ = GetSel(self._obj_)
startLine = LineFromChar(self._obj_, start)
line = GetLine(self._obj_, startLine)
realCol = start - LineIndex(self._obj_, startLine)
curCol = 0
for ch in line[begin:realCol]
if ch == "\t"
curCol = ((curCol / self.tabSize) + 1)*self.tabSize
else
curCol = curCol + 1
end
end
nextColumn = ((curCol / self.indentSize) + 1)*self.indentSize
ins = nothing
if self.bSmartTabs
if realCol == 0
lookLine = startLine - 1
while lookLine >= 0
check = GetLine(self._obj_, lookLine)[1:1]
if check ∈ ["\t", " "]
ins = check
has_break = true
break;
end
lookLine = lookLine - 1
end
else
check = line[realCol]
if check ∈ ["\t", " "]
ins = check
end
end
end
if ins === nothing
if self.bUseTabs && (nextColumn % self.tabSize) == 0
ins = "\t"
else
ins = " "
end
end
if ins == " "
ins = ins*(nextColumn - curCol)
end
ReplaceSel(self._obj_, ins)
end

function BlockDent(self::EditorView, isIndent, startLine, endLine)::Int64
#= Indent/Undent all lines specified =#
if !CheckMakeDocumentWritable(GetDocument(self))
return 0
end
tabSize = self.tabSize
info = _PrepareUserStateChange(self)
try
for lineNo in startLine:endLine - 1
pos = LineIndex(self._obj_, lineNo)
SetSel(self._obj_, pos, pos)
if isIndent
Indent(self)
else
line = GetLine(self._obj_, lineNo)
try
noToDel = 0
if line[1] == "\t"
noToDel = 1
elseif line[1] == " "
has_break = false
for noToDel in 0:tabSize - 1
if line[noToDel + 1] != " "
has_break = true
break;
end
end
if has_break != true
noToDel = tabSize
end
end
if noToDel != 0
SetSel(self._obj_, pos, pos + noToDel)
Clear(self._obj_)
end
catch exn
if exn isa IndexError
#= pass =#
end
end
end
end
finally
_EndUserStateChange(self, info)
end
SetModifiedFlag(GetDocument(self), 1)
SetSel(self._obj_, LineIndex(self, startLine), LineIndex(self, endLine))
end

function GotoLine(self::EditorView, lineNo = nothing)::Int64
try
if lineNo === nothing
lineNo = parse(Int, input("Enter Line Number"))
end
catch exn
if exn isa (ValueError, KeyboardInterrupt)
return 0
end
end
GetLineCount(self)
charNo = LineIndex(self, lineNo - 1)
SetSel(self, charNo)
end

function HookHandlers(self::EditorView)
HookMessage(self, self.OnCheckExternalDocumentUpdated, MSG_CHECK_EXTERNAL_FILE)
HookMessage(self, self.OnRClick, win32con.WM_RBUTTONDOWN)
HookMessage(self, self.OnSetFocus, win32con.WM_SETFOCUS)
HookMessage(self, self.OnKeyDown, win32con.WM_KEYDOWN)
HookKeyStroke(self, self.OnKeyCtrlY, 25)
HookKeyStroke(self, self.OnKeyCtrlG, 7)
HookKeyStroke(self, self.OnKeyTab, 9)
HookKeyStroke(self, self.OnKeyEnter, 13)
HookCommand(self, self.OnCmdLocateFile, ID_LOCATE_FILE)
HookCommand(self, self.OnCmdGotoLine, ID_GOTO_LINE)
HookCommand(self, self.OnEditPaste, afxres.ID_EDIT_PASTE)
HookCommand(self, self.OnEditCut, afxres.ID_EDIT_CUT)
end

function OnSetFocus(self::EditorView, msg)
OnCheckExternalDocumentUpdated(self, msg)
end

function OnRClick(self::EditorView, params)::Int64
menu = CreatePopupMenu(win32ui)
line = strip(GetLine(self._obj_))
flags = win32con.MF_STRING | win32con.MF_ENABLED
if match(patImport, line) == length(line)
AppendMenu(menu, flags, ID_LOCATE_FILE, "&Locate %s.py" % group(patImport, "name"))
AppendMenu(menu, win32con.MF_SEPARATOR)
end
AppendMenu(menu, flags, win32ui.ID_EDIT_UNDO, "&Undo")
AppendMenu(menu, win32con.MF_SEPARATOR)
AppendMenu(menu, flags, win32ui.ID_EDIT_CUT, "Cu&t")
AppendMenu(menu, flags, win32ui.ID_EDIT_COPY, "&Copy")
AppendMenu(menu, flags, win32ui.ID_EDIT_PASTE, "&Paste")
AppendMenu(menu, flags, win32con.MF_SEPARATOR)
AppendMenu(menu, flags, win32ui.ID_EDIT_SELECT_ALL, "&Select all")
AppendMenu(menu, flags, win32con.MF_SEPARATOR)
AppendMenu(menu, flags, ID_GOTO_LINE, "&Goto line...")
TrackPopupMenu(menu, params[6])
return 0
end

function OnCmdGotoLine(self::EditorView, cmd, code)::Int64
GotoLine(self)
return 0
end

function OnCmdLocateFile(self::EditorView, cmd, code)::Int64
modName = group(patImport, "name")
if !(modName)
return 0
end
fileName = LocatePythonFile(win32com_.gen_py.framework.scriptutils, modName)
if fileName === nothing
SetStatusText(win32ui, "Can\'t locate module %s" % modName)
else
OpenDocumentFile(GetApp(win32ui), fileName)
end
return 0
end

function OnKeyEnter(self::EditorView, key)::Int64
if !CheckMakeDocumentWritable(GetDocument(self))
return 0
end
curLine = GetLine(self._obj_)
ReplaceSel(self._obj_, "\r\n")
res = match(patIndent, curLine, 0)
if res > 0 && strip(curLine)
curIndent = group(patIndent, 1)
ReplaceSel(self._obj_, curIndent)
end
return 0
end

function OnKeyCtrlY(self::EditorView, key)::Int64
if !CheckMakeDocumentWritable(GetDocument(self))
return 0
end
CutCurLine(self)
return 0
end

function OnKeyCtrlG(self::EditorView, key)::Int64
GotoLine(self)
return 0
end

function OnKeyTab(self::EditorView, key)::Int64
if !CheckMakeDocumentWritable(GetDocument(self))
return 0
end
start, end_ = GetSel(self._obj_)
if start == end_
Indent(self)
return 0
end
if start > end_
start, end_ = (end_, start)
end
startLine = LineFromChar(self._obj_, start)
endLine = LineFromChar(self._obj_, end_)
BlockDent(self, GetKeyState(win32api, win32con.VK_SHIFT) >= 0, startLine, endLine)
return 0
end

function OnEditPaste(self::EditorView, id, code)
return CheckMakeDocumentWritable(GetDocument(self))
end

function OnEditCut(self::EditorView, id, code)
return CheckMakeDocumentWritable(GetDocument(self))
end

function OnKeyDown(self::EditorView, msg)::Int64
key = msg[3]
if GetKeyState(win32api, win32con.VK_CONTROL) & 32768
modList = MODIFYING_VK_KEYS_CTRL
elseif GetKeyState(win32api, win32con.VK_MENU) & 32768
modList = MODIFYING_VK_KEYS_ALT
else
modList = MODIFYING_VK_KEYS
end
if key ∈ modList
return CheckMakeDocumentWritable(GetDocument(self))
end
return 1
end

function OnCheckExternalDocumentUpdated(self::EditorView, msg)
if self._obj_ === nothing || self.bCheckingFile
return
end
self.bCheckingFile = 1
CheckExternalDocumentUpdated(GetDocument(self))
self.bCheckingFile = 0
end

using template: EditorTemplateBase
mutable struct EditorTemplate <: AbstractEditorTemplate
makeDoc
makeFrame
makeView
res

            EditorTemplate(res = win32ui.IDR_TEXTTYPE, makeDoc = nothing, makeFrame = nothing, makeView = nothing) = begin
                if makeDoc === nothing
makeDoc = EditorDocument
end
if makeView === nothing
makeView = EditorView
end
EditorTemplateBase.__init__(self, res, makeDoc, makeFrame, makeView)
                new(res , makeDoc , makeFrame , makeView )
            end
end
function _CreateDocTemplate(self::EditorTemplate, resourceId)
return CreateRichEditDocTemplate(win32ui, resourceId)
end

function CreateWin32uiDocument(self::EditorTemplate)
return DoCreateRichEditDoc(self)
end

function Create(fileName = nothing, title = nothing, template = nothing)
return OpenDocumentFile(editorTemplate, fileName)
end

using win32com_.gen_py.framework.editor: GetDefaultEditorModuleName
prefModule = GetDefaultEditorModuleName()
if __name__ == prefModule
try
RemoveDocTemplate(GetApp(win32ui), editorTemplate)
catch exn
if exn isa (NameError, win32ui.error)
#= pass =#
end
end
editorTemplate = EditorTemplate()
AddDocTemplate(GetApp(win32ui), editorTemplate)
end