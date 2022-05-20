using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")

import _thread
import sysconfig


using win32com_.gen_py.mfc: docview, dialog, window
import win32con
import string
import glob
import stat
include("scriptutils.jl")
function getsubdirs(d)::Vector
dlist = []
flist = glob(glob, d + "\\*")
for f in flist
if isdir(os.path, f)
push!(dlist, f)
dlist = dlist + getsubdirs(f)
end
end
return dlist
end

abstract type Abstractdirpath end
abstract type AbstractTheTemplate <: Abstractdocview.RichEditDocTemplate end
abstract type AbstractTheFrame <: Abstractwindow.MDIChildWnd end
abstract type AbstractTheDocument <: Abstractdocview.RichEditDoc end
abstract type AbstractTheView <: Abstractdocview.RichEditView end
abstract type AbstractTheDialog <: Abstractdialog.Dialog end
abstract type AbstractTheParamsDialog <: Abstractdialog.Dialog end
mutable struct dirpath <: Abstractdirpath
dirs::Vector
recurse::Int64

            dirpath(str, recurse = 0) = begin
                for d in dp
if os.path.isdir(d)
d = d.lower()
if d ∉ dirs
dirs[d] = nothing
if recurse
subdirs = getsubdirs(d)
for sd in subdirs
sd = sd.lower()
if sd ∉ dirs
dirs[sd] = nothing
end
end
end
end
elseif os.path.isfile(d)
#= pass =#
else
x = nothing
if d ∈ os.environ
x = dirpath(os.environ[d])
elseif d[begin:5] == "HKEY_"
keystr = d.split("\\")
try
root = eval("win32con." + keystr[0])
catch exn
win32ui.MessageBox("Can\'t interpret registry key name \'%s\'" % keystr[0])
end
try
subkey = "\\".join(keystr[1:end])
val = win32api.RegQueryValue(root, subkey)
if val
x = dirpath(val)
else
win32ui.MessageBox("Registry path \'%s\' did not return a path entry" % d)
end
catch exn
win32ui.MessageBox("Can\'t interpret registry key value: %s" % keystr[1:end])
end
else
win32ui.MessageBox("Directory \'%s\' not found" % d)
end
if x
for xd in x
if xd ∉ dirs
dirs[xd] = nothing
if recurse
subdirs = getsubdirs(xd)
for sd in subdirs
sd = sd.lower()
if sd ∉ dirs
dirs[sd] = nothing
end
end
end
end
end
end
end
end
for d in dirs.keys()
dirs.append(d)
end
                new(str, recurse )
            end
end
function __getitem__(self::dirpath, key)::Vector
return self.dirs[key + 1]
end

function __len__(self::dirpath)::Int64
return length(self.dirs)
end

function __setitem__(self::dirpath, key, value)
self.dirs[key + 1] = value
end

function __delitem__(self::dirpath, key)
#Delete Unsupported
del(self.dirs)
end

function __getslice__(self::dirpath, lo, hi)::Vector
return self.dirs[lo + 1:hi]
end

function __setslice__(self::dirpath, lo, hi, seq)
self.dirs[lo + 1:hi] = seq
end

function __delslice__(self::dirpath, lo, hi)
#Delete Unsupported
del(self.dirs)
end

function __add__(self::dirpath, other)::Vector
if type_(other) == type_(self) || type_(other) == type_([])
return self.dirs + other.dirs
end
end

function __radd__(self::dirpath, other)::Vector
if type_(other) == type_(self) || type_(other) == type_([])
return other.dirs + self.dirs
end
end

regexGrep = compile(re, "^(..[^\\(:]+)?[\\(:](\\d+)[\\):]:?\\s*(.*)")
BUTTON = 128
EDIT = 129
STATIC = 130
LISTBOX = 131
SCROLLBAR = 132
COMBOBOX = 133
mutable struct TheTemplate <: AbstractTheTemplate
docparams

            TheTemplate() = begin
                docview.RichEditDocTemplate.__init__(self, win32ui.IDR_TEXTTYPE, TheDocument, TheFrame, TheView)
SetDocStrings("\nPychecker\nPychecker\nPychecker params (*.pychecker)\n.pychecker\n\n\n")
win32ui.GetApp().AddDocTemplate(self)
                new()
            end
end
function MatchDocType(self::TheTemplate, fileName, fileType)
doc = FindOpenDocument(self, fileName)
if doc
return doc
end
ext = lower(splitext(os.path, fileName)[2])
if ext == ".pychecker"
return win32ui.CDocTemplate_Confidence_yesAttemptNative
end
return win32ui.CDocTemplate_Confidence_noAttempt
end

function setParams(self::TheTemplate, params)
self.docparams = params
end

function readParams(self::TheTemplate)
tmp = self.docparams
self.docparams = nothing
return tmp
end

mutable struct TheFrame <: AbstractTheFrame
wnd

            TheFrame(wnd = nothing) = begin
                window.MDIChildWnd.__init__(self, wnd)
                new(wnd )
            end
end

mutable struct TheDocument <: AbstractTheDocument
dirpattern::String
filpattern::String
greppattern::String
casesensitive::Int64
recurse::Int64
verbose::Int64
dp::Abstractdirpath
fplist
dpndx::Int64
fpndx::Int64
fndx::Int64
flist
result
idleHandler
threadPycheckerRun

            TheDocument(template) = begin
                docview.RichEditDoc.__init__(self, template)
                new(template)
            end
end
function OnOpenDocument(self::TheDocument, fnm)::Int64
try
params = read(readline(fnm))
catch exn
params = nothing
end
setInitParams(self, params)
return OnNewDocument(self)
end

function OnCloseDocument(self::TheDocument)
try
DeleteIdleHandler(GetApp(win32ui), self.idleHandler)
catch exn
#= pass =#
end
return OnCloseDocument(self._obj_)
end

function saveInitParams(self::TheDocument)
paramstr = "\t\t\t%d\t%d" % (self.casesensitive, self.recurse)
WriteProfileVal(win32ui, "Pychecker", "Params", paramstr)
end

function setInitParams(self::TheDocument, paramstr)
if paramstr === nothing
paramstr = GetProfileVal(win32ui, "Pychecker", "Params", "\t\t\t1\t0\t0")
end
params = split(paramstr, "\t")
if length(params) < 3
params = append!(params, repeat([""],(3 - length(params))))
end
if length(params) < 6
params = append!(params, repeat([0],(6 - length(params))))
end
self.dirpattern = params[1]
self.filpattern = params[2]
self.greppattern = params[3] || "-#1000 --only"
self.casesensitive = parse(Int, params[4])
self.recurse = parse(Int, params[5])
self.verbose = parse(Int, params[6])
if !(self.dirpattern)
try
editor = GetEditorView(MDIGetActive(GetMainFrame(win32ui))[1])
self.dirpattern = abspath(os.path, dirname(os.path, GetPathName(GetDocument(editor))))
catch exn
if exn isa (AttributeError, win32ui.error)
self.dirpattern = getcwd(os)
end
end
end
if !(self.filpattern)
try
editor = GetEditorView(MDIGetActive(GetMainFrame(win32ui))[1])
self.filpattern = GetPathName(GetDocument(editor))
catch exn
if exn isa AttributeError
self.filpattern = "*.py"
end
end
end
end

function OnNewDocument(self::TheDocument)::Int64
if self.dirpattern == ""
setInitParams(self, readParams(greptemplate))
end
d = TheDialog(self.dirpattern, self.filpattern, self.greppattern, self.casesensitive, self.recurse, self.verbose)
if DoModal(d) == win32con.IDOK
self.dirpattern = d["dirpattern"]
self.filpattern = d["filpattern"]
self.greppattern = d["greppattern"]
doSearch(self)
saveInitParams(self)
return 1
end
return 0
end

function doSearch(self::TheDocument)
self.dp = dirpath(self.dirpattern, self.recurse)
SetTitle(self, "Pychecker Run \'%s\' (options: %s)" % (self.filpattern, self.greppattern))
Append(GetFirstView(self), "#Pychecker Run in " * self.dirpattern * ("  %s\n" % asctime(time)))
if self.verbose != 0
Append(GetFirstView(self), ("#   =" + repr(self.dp.dirs)) * "\n")
end
Append(GetFirstView(self), "# Files   " * self.filpattern * "\n")
Append(GetFirstView(self), "# Options " * self.greppattern * "\n")
self.fplist = split(self.filpattern, ";")
Append(GetFirstView(self), "# Running...  ( double click on result lines in order to jump to the source code ) \n")
SetStatusText(win32ui, "Pychecker running.  Please wait...", 0)
self.dpndx = 0
self.fpndx = 0
self.fndx = -1
if !(self.dp)
Append(GetFirstView(self), "# ERROR: \'%s\' does not resolve to any search locations" % self.dirpattern)
SetModifiedFlag(self, 0)
else
self.flist = reduce(operator.add, collect(map(glob.glob, self.fplist)))
startPycheckerRun(self)
end
end

function idleHandler(self::TheDocument, handler, count)::Int64
sleep(time, 0.001)
if self.result != nothing
DeleteIdleHandler(GetApp(win32ui), self.idleHandler)
return 0
end
return 1
end

function startPycheckerRun(self::TheDocument)
self.result = nothing
old = SetCursor(win32api, LoadCursor(win32api, 0, win32con.IDC_APPSTARTING))
AddIdleHandler(GetApp(win32ui), self.idleHandler)
start_new(_thread, self.threadPycheckerRun, ())
end

function threadPycheckerRun(self::TheDocument)
result = ""
rc = -1
try
options = self.greppattern
files = join(self.flist, " ")
py = join
if !isfile(os.path, py)
if "64 bit" ∈ sys.version
py = join
else
py = join
end
end
try
py = GetShortPathName(win32api, py)
catch exn
if exn isa win32api.error
py = ""
end
end
pychecker = join
if !isfile(os.path, py)
result = "Can\'t find python.exe!\n"
elseif !isfile(os.path, pychecker)
result = "Can\'t find checker.py - please install pychecker (or run \'setup.py install\' if you have the source version)\n"
else
cmd = "%s \"%s\" %s %s 2>&1" % (py, pychecker, options, files)
result = read(popen(os, cmd))
end
Append(GetFirstView(self), result)
finally
self.result = result
println("== Pychecker run finished ==")
Append(GetFirstView(self), "\n" * "== Pychecker run finished ==")
SetModifiedFlag(self, 0)
end
end

function _inactive_idleHandler(self::TheDocument, handler, count)::Int64
self.fndx = self.fndx + 1
if self.fndx < length(self.flist)
f = self.flist[self.fndx + 1]
if self.verbose != 0
Append(GetFirstView(self), ("# .." + f) + "\n")
end
SetStatusText(win32ui, "Searching " + f, 0)
lines = readlines(readline(f))
for i in 0:length(lines) - 1
line = lines[i + 1]
if search(self.pat, line) != nothing
Append(GetFirstView(self), (((f + "(") + repr(i + 1)) + ") ") + line)
end
end
else
self.fndx = -1
self.fpndx = self.fpndx + 1
if self.fpndx < length(self.fplist)
self.flist = glob(glob, (self.dp[self.dpndx + 1] + "\\") + self.fplist[self.fpndx + 1])
else
self.fpndx = 0
self.dpndx = self.dpndx + 1
if self.dpndx < length(self.dp)
self.flist = glob(glob, (self.dp[self.dpndx + 1] + "\\") + self.fplist[self.fpndx + 1])
else
SetStatusText(win32ui, "Search complete.", 0)
SetModifiedFlag(self, 0)
try
DeleteIdleHandler(GetApp(win32ui), self.idleHandler)
catch exn
#= pass =#
end
return 0
end
end
end
return 1
end

function GetParams(self::TheDocument)::String
return ((self.dirpattern * "\t" * self.filpattern * "\t" * self.greppattern * "\t" + repr(self.casesensitive)) * "\t" + repr(self.recurse)) * "\t" + repr(self.verbose)
end

function OnSaveDocument(self::TheDocument, filename)::Int64
savefile = readline(filename)
txt = GetParams(self) * "\n"
write(savefile, txt)
close(savefile)
SetModifiedFlag(self, 0)
return 1
end

ID_OPEN_FILE = 58624
ID_PYCHECKER = 58625
ID_SAVERESULTS = 1282
ID_TRYAGAIN = 1283
ID_ADDCOMMENT = 1284
ID_ADDPYCHECKNO2 = 1285
mutable struct TheView <: AbstractTheView
fnm
lnnum::Int64
OnRClick
OnCmdOpenFile
OnCmdThe
OnCmdSave
OnTryAgain
OnAddComment
OnLDblClick

            TheView(doc) = begin
                docview.RichEditView.__init__(self, doc)
SetWordWrap(win32ui.CRichEditView_WrapNone)
HookHandlers()
                new(doc)
            end
end
function OnInitialUpdate(self::TheView)
rc = OnInitialUpdate(self._obj_)
format = (-402653169, 0, 200, 0, 0, 0, 49, "Courier New")
SetDefaultCharFormat(self, format)
return rc
end

function HookHandlers(self::TheView)
HookMessage(self, self.OnRClick, win32con.WM_RBUTTONDOWN)
HookCommand(self, self.OnCmdOpenFile, ID_OPEN_FILE)
HookCommand(self, self.OnCmdThe, ID_PYCHECKER)
HookCommand(self, self.OnCmdSave, ID_SAVERESULTS)
HookCommand(self, self.OnTryAgain, ID_TRYAGAIN)
HookCommand(self, self.OnAddComment, ID_ADDCOMMENT)
HookCommand(self, self.OnAddComment, ID_ADDPYCHECKNO2)
HookMessage(self, self.OnLDblClick, win32con.WM_LBUTTONDBLCLK)
end

function OnLDblClick(self::TheView, params)::Int64
line = GetLine(self)
regexGrepResult = match(regexGrep, line)
if regexGrepResult
fname = group(regexGrepResult, 1)
line = parse(Int, group(regexGrepResult, 2))
JumpToDocument(scriptutils, fname, line)
return 0
end
return 1
end

function OnRClick(self::TheView, params)::Int64
menu = CreatePopupMenu(win32ui)
flags = win32con.MF_STRING | win32con.MF_ENABLED
lineno = LineFromChar(self._obj_, -1)
line = GetLine(self._obj_, lineno)
regexGrepResult = match(regexGrep, line)
charstart, charend = GetSel(self._obj_)
if regexGrepResult
self.fnm = group(regexGrepResult, 1)
self.lnnum = parse(Int, group(regexGrepResult, 2))
AppendMenu(menu, flags, ID_OPEN_FILE, "&Open " + self.fnm)
AppendMenu(menu, flags, ID_ADDCOMMENT, "&Add to source: Comment Tag/#\$pycheck_no ..")
AppendMenu(menu, flags, ID_ADDPYCHECKNO2, "&Add to source: Specific #\$pycheck_no=%(errtext)s ..")
AppendMenu(menu, win32con.MF_SEPARATOR)
end
AppendMenu(menu, flags, ID_TRYAGAIN, "&Try Again")
AppendMenu(menu, flags, win32ui.ID_EDIT_CUT, "Cu&t")
AppendMenu(menu, flags, win32ui.ID_EDIT_COPY, "&Copy")
AppendMenu(menu, flags, win32ui.ID_EDIT_PASTE, "&Paste")
AppendMenu(menu, flags, win32con.MF_SEPARATOR)
AppendMenu(menu, flags, win32ui.ID_EDIT_SELECT_ALL, "&Select all")
AppendMenu(menu, flags, win32con.MF_SEPARATOR)
AppendMenu(menu, flags, ID_SAVERESULTS, "Sa&ve results")
TrackPopupMenu(menu, params[6])
return 0
end

function OnAddComment(self::TheView, cmd, code)::Int64
addspecific = cmd == ID_ADDPYCHECKNO2
_ = collect(GetSel(self))
sort(_)
start, end_ = _
line_start, line_end = (LineFromChar(self, start), LineFromChar(self, end_))
first = 1
for i in line_start:line_end
line = GetLine(self, i)
m = match(regexGrep, line)
if m
if first
first = 0
cmnt = GetSimpleInput(dialog, "Add to %s lines" % ((line_end - line_start) + 1), addspecific && "  #\$pycheck_no=%(errtext)s" || "  #\$pycheck_no")
if !(cmnt)
return 0
end
end
fname = group(m, 1)
line = parse(Int, group(m, 2))
view = JumpToDocument(scriptutils, fname, line)
pos = LineIndex(view, line) - 1
if GetTextRange(view, pos - 1, pos) ∈ ("\r", "\n")
pos -= 1
end
SetSel(view, pos, pos)
errtext = group(m, 3)
if start != end_ && line_start === line_end
errtext = GetSelText(self)
end
errtext = repr(replace(escape(re, errtext), "\\ ", " "))
ReplaceSel(view, addspecific && cmnt % locals() || cmnt)
end
end
return 0
end

function OnCmdOpenFile(self::TheView, cmd, code)::Int64
doc = OpenDocumentFile(GetApp(win32ui), self.fnm)
if doc
vw = GetFirstView(doc)
try
GotoLine(vw, Int(self.lnnum))
catch exn
#= pass =#
end
end
return 0
end

function OnCmdThe(self::TheView, cmd, code)::Int64
curparamsstr = GetParams(GetDocument(self))
params = split(curparamsstr, "\t")
params[3] = self.sel
setParams(greptemplate, join(params, "\t"))
OpenDocumentFile(greptemplate)
return 0
end

function OnTryAgain(self::TheView, cmd, code)::Int64
setParams(greptemplate, GetParams(GetDocument(self)))
OpenDocumentFile(greptemplate)
return 0
end

function OnCmdSave(self::TheView, cmd, code)::Int64
flags = win32con.OFN_OVERWRITEPROMPT
dlg = CreateFileDialog(win32ui, 0, nothing, nothing, flags, "Text Files (*.txt)|*.txt||", self)
SetOFNTitle(dlg, "Save Results As")
if DoModal(dlg) == win32con.IDOK
pn = GetPathName(dlg)
SaveFile(self._obj_, pn)
end
return 0
end

function Append(self::TheView, strng)
numlines = GetLineCount(self)
endpos = LineIndex(self, numlines - 1) + length(GetLine(self, numlines - 1))
SetSel(self, endpos, endpos)
ReplaceSel(self, strng)
end

mutable struct TheDialog <: AbstractTheDialog


            TheDialog(dp, fp, gp, cs, r, v) = begin
                tmp.append([STATIC, "Files:", -1, (7, 7, 50, 9), CS])
tmp.append([EDIT, gp, 103, (52, 7, 144, 11), ((CS | win32con.WS_TABSTOP) | win32con.ES_AUTOHSCROLL) | win32con.WS_BORDER])
tmp.append([STATIC, "Directories:", -1, (7, 20, 50, 9), CS])
tmp.append([EDIT, dp, 102, (52, 20, 128, 11), ((CS | win32con.WS_TABSTOP) | win32con.ES_AUTOHSCROLL) | win32con.WS_BORDER])
tmp.append([BUTTON, "...", 110, (182, 20, 16, 11), (CS | win32con.BS_PUSHBUTTON) | win32con.WS_TABSTOP])
tmp.append([STATIC, "Options:", -1, (7, 33, 50, 9), CS])
tmp.append([EDIT, fp, 101, (52, 33, 128, 11), ((CS | win32con.WS_TABSTOP) | win32con.ES_AUTOHSCROLL) | win32con.WS_BORDER])
tmp.append([BUTTON, "...", 111, (182, 33, 16, 11), (CS | win32con.BS_PUSHBUTTON) | win32con.WS_TABSTOP])
tmp.append([BUTTON, "OK", win32con.IDOK, (166, 53, 32, 12), (CS | win32con.BS_DEFPUSHBUTTON) | win32con.WS_TABSTOP])
tmp.append([BUTTON, "Cancel", win32con.IDCANCEL, (166, 67, 32, 12), (CS | win32con.BS_PUSHBUTTON) | win32con.WS_TABSTOP])
dialog.Dialog.__init__(self, tmp)
AddDDX(101, "greppattern")
AddDDX(102, "dirpattern")
AddDDX(103, "filpattern")
HookCommand(OnMoreDirectories, 110)
HookCommand(OnMoreFiles, 111)
                new(dp, fp, gp, cs, r, v)
            end
end
function OnMoreDirectories(self::TheDialog, cmd, code)
getMore(self, "Pychecker\\Directories", "dirpattern")
end

function OnMoreFiles(self::TheDialog, cmd, code)
getMore(self, "Pychecker\\File Types", "filpattern")
end

function getMore(self::TheDialog, section, key)
UpdateData(self, 1)
ini = GetProfileFileName(win32ui)
secitems = GetProfileSection(win32api, section, ini)
items = []
for secitem in secitems
push!(items, split(secitem, "=")[2])
end
dlg = TheParamsDialog(items)
if DoModal(dlg) == win32con.IDOK
itemstr = join(getItems(dlg), ";")
self._obj_.data[key + 1] = itemstr
i = 0
newitems = getNew(dlg)
if newitems
items = items + newitems
for item in items
WriteProfileVal(win32api, section, repr(i), item, ini)
i = i + 1
end
end
UpdateData(self, 0)
end
end

function OnOK(self::TheDialog)
UpdateData(self, 1)
for (id, name) in [(101, "greppattern"), (102, "dirpattern"), (103, "filpattern")]
if !(self[name + 1])
SetFocus(GetDlgItem(self, id))
MessageBeep(win32api)
SetStatusText(win32ui, "Please enter a value")
return
end
end
OnOK(self._obj_)
end

mutable struct TheParamsDialog <: AbstractTheParamsDialog
items
newitems::Vector
selections

            TheParamsDialog(items) = begin
                tmp.append([LISTBOX, "", 107, (7, 7, 150, 72), ((((CS | win32con.LBS_MULTIPLESEL) | win32con.LBS_STANDARD) | win32con.LBS_HASSTRINGS) | win32con.WS_TABSTOP) | win32con.LBS_NOTIFY])
tmp.append([BUTTON, "OK", win32con.IDOK, (167, 7, 32, 12), (CS | win32con.BS_DEFPUSHBUTTON) | win32con.WS_TABSTOP])
tmp.append([BUTTON, "Cancel", win32con.IDCANCEL, (167, 23, 32, 12), (CS | win32con.BS_PUSHBUTTON) | win32con.WS_TABSTOP])
tmp.append([STATIC, "New:", -1, (2, 83, 15, 12), CS])
tmp.append([EDIT, "", 108, (18, 83, 139, 12), ((CS | win32con.WS_TABSTOP) | win32con.ES_AUTOHSCROLL) | win32con.WS_BORDER])
tmp.append([BUTTON, "Add", 109, (167, 83, 32, 12), (CS | win32con.BS_PUSHBUTTON) | win32con.WS_TABSTOP])
dialog.Dialog.__init__(self, tmp)
HookCommand(OnAddItem, 109)
HookCommand(OnListDoubleClick, 107)
                new(items)
            end
end
function OnInitDialog(self::TheParamsDialog)
lb = GetDlgItem(self, 107)
for item in self.items
AddString(lb, item)
end
return OnInitDialog(self._obj_)
end

function OnAddItem(self::TheParamsDialog, cmd, code)::Int64
eb = GetDlgItem(self, 108)
item = GetLine(eb, 0)
append(self.newitems, item)
lb = GetDlgItem(self, 107)
i = AddString(lb, item)
SetSel(lb, i, 1)
return 1
end

function OnListDoubleClick(self::TheParamsDialog, cmd, code)::Int64
if code == win32con.LBN_DBLCLK
OnOK(self)
return 1
end
end

function OnOK(self::TheParamsDialog)
lb = GetDlgItem(self, 107)
self.selections = GetSelTextItems(lb)
OnOK(self._obj_)
end

function getItems(self::TheParamsDialog)
return self.selections
end

function getNew(self::TheParamsDialog)::Vector
return self.newitems
end

try
RemoveDocTemplate(GetApp(win32ui), greptemplate)
catch exn
if exn isa NameError
#= pass =#
end
end
greptemplate = TheTemplate()