using Printf
using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
import win32com_.gen_py.debugger
using win32com_.gen_py.mfc: docview, object
using win32com_.gen_py.framework.editor: GetEditorOption


import win32con
import string


import shutil
BAK_NONE = 0
BAK_DOT_BAK = 1
BAK_DOT_BAK_TEMP_DIR = 2
abstract type AbstractEditorDocumentBase <: AbstractParentEditorDocument end
abstract type AbstractFileWatchingThread <: Abstractwin32com_.gen_py.mfc.thread.WinThread end
BAK_DOT_BAK_BAK_DIR = 3
MSG_CHECK_EXTERNAL_FILE = win32con.WM_USER + 1999
import win32com_.gen_py.scintilla.document
ParentEditorDocument = win32com_.gen_py.scintilla.document.CScintillaDocument
mutable struct EditorDocumentBase <: AbstractEditorDocumentBase
bAutoReload
bDeclinedReload::Int64
fileStat
bReportedFileNotFound::Int64
bakFileType
watcherThread::AbstractFileWatchingThread
scModuleName
scModule

            EditorDocumentBase(template) = begin
                watcherThread.CreateThread()
ParentEditorDocument.__init__(self, template, template.CreateWin32uiDocument())
                new(template)
            end
end
function OnCloseDocument(self::EditorDocumentBase)
SignalStop(self.watcherThread)
return OnCloseDocument(self._obj_)
end

function OnSaveDocument(self::EditorDocumentBase, fileName)::Int64
SetStatusText(win32ui, "Saving file...", 1)
dir, basename = split(os.path, fileName)
if self.bakFileType == BAK_DOT_BAK
bakFileName = ((dir + "\\") + splitext(os.path, basename)[1]) * ".bak"
elseif self.bakFileType == BAK_DOT_BAK_TEMP_DIR
bakFileName = ((GetTempPath(win32api) + "\\") + splitext(os.path, basename)[1]) * ".bak"
elseif self.bakFileType == BAK_DOT_BAK_BAK_DIR
tempPath = join
try
mkdir(os, tempPath, 0)
catch exn
if exn isa os.error
#= pass =#
end
end
bakFileName = join
end
try
std::fs::remove_file(bakFileName)
catch exn
if exn isa (os.error, NameError)
#= pass =#
end
end
try
copy2(shutil, fileName, bakFileName)
catch exn
if exn isa (os.error, NameError, IOError)
#= pass =#
end
end
try
SaveFile(self, fileName)
catch exn
 let details = exn
if details isa IOError
MessageBox(win32ui, "Error - could not save file\r\n\r\n%s" % details)
return 0
end
end
 let details = exn
if details isa (UnicodeEncodeError, LookupError)
rc = MessageBox(win32ui, ("Encoding failed: \r\n%s" % details) * "\r\nPlease add desired source encoding as first line of file, eg \r\n" * "# -*- coding: mbcs -*-\r\n\r\n" * "If you continue, the file will be saved as binary and will\r\n" * "not be valid in the declared encoding.\r\n\r\n" * "Save the file as binary with an invalid encoding?", "File save failed", win32con.MB_YESNO | win32con.MB_DEFBUTTON2)
if rc == win32con.IDYES
try
SaveFile(self, fileName, "latin-1")
catch exn
 let details = exn
if details isa IOError
MessageBox(win32ui, "Error - could not save file\r\n\r\n%s" % details)
return 0
end
end
end
else
return 0
end
end
end
end
SetModifiedFlag(self, 0)
self.bDeclinedReload = 0
AddToRecentFileList(win32ui, fileName)
SetPathName(self, fileName)
SetStatusText(win32ui, "Ready")
_DocumentStateChanged(self)
return 1
end

function FinalizeViewCreation(self::EditorDocumentBase, view)
FinalizeViewCreation(ParentEditorDocument, self)
if view == GetFirstView(self)
_DocumentStateChanged(self)
if view.bFolding && GetEditorOption("Fold On Open", 0)
FoldTopLevelEvent(view)
end
end
end

function HookViewNotifications(self::EditorDocumentBase, view)
HookViewNotifications(ParentEditorDocument, self)
end

function ReloadDocument(self::EditorDocumentBase)
#= Reloads the document from disk.  Assumes the file has
        been saved and user has been asked if necessary - it just does it!
         =#
SetStatusText(win32ui, "Reloading document.  Please wait...", 1)
SetModifiedFlag(self, 0)
views = GetAllViews(self)
states = []
for view in views
try
info = _PrepareUserStateChange(view)
catch exn
if exn isa AttributeError
info = nothing
end
end
push!(states, info)
end
OnOpenDocument(self, GetPathName(self))
for (view, info) in zip(views, states)
if info != nothing
_EndUserStateChange(view, info)
end
end
_DocumentStateChanged(self)
SetStatusText(win32ui, "Document reloaded.")
end

function CheckExternalDocumentUpdated(self::EditorDocumentBase)
if self.bDeclinedReload || !GetPathName(self)
return
end
try
newstat = stat(os, GetPathName(self))
catch exn
 let exc = exn
if exc isa os.error
if !(self.bReportedFileNotFound) != 0
@printf("The file \'%s\' is open for editing, but\nchecking it for changes caused the error: %s\n", GetPathName(self), exc.strerror)
self.bReportedFileNotFound = 1
end
return
end
end
end
if self.bReportedFileNotFound != 0
@printf("The file \'%s\' has re-appeared - continuing to watch for changes...\n", GetPathName(self))
self.bReportedFileNotFound = 0
end
changed = self.fileStat === nothing || self.fileStat[1] != newstat[1] || self.fileStat[7] != newstat[7] || self.fileStat[9] != newstat[9] || self.fileStat[10] != newstat[10]
if changed
question = nothing
if IsModified(self)
question = "%s\r\n\r\nThis file has been modified outside of the source editor.\r\nDo you want to reload it and LOSE THE CHANGES in the source editor?" % GetPathName(self)
mbStyle = win32con.MB_YESNO | win32con.MB_DEFBUTTON2
elseif !(self.bAutoReload)
question = "%s\r\n\r\nThis file has been modified outside of the source editor.\r\nDo you want to reload it?" % GetPathName(self)
mbStyle = win32con.MB_YESNO
end
if question
rc = MessageBox(win32ui, question, nothing, mbStyle)
if rc != win32con.IDYES
self.bDeclinedReload = 1
return
end
end
ReloadDocument(self)
end
end

function _DocumentStateChanged(self::EditorDocumentBase)
#= Called whenever the documents state (on disk etc) has been changed
        by the editor (eg, as the result of a save operation)
         =#
if GetPathName(self)
try
self.fileStat = stat(os, GetPathName(self))
catch exn
if exn isa os.error
self.fileStat = nothing
end
end
else
self.fileStat = nothing
end
_DocumentStateChanged(self.watcherThread)
_UpdateUIForState(self)
_ApplyOptionalToViews(self, "_UpdateUIForState")
_ApplyOptionalToViews(self, "SetReadOnly", _IsReadOnly(self))
_ApplyOptionalToViews(self, "SCISetSavePoint")
if win32com_.gen_py.debugger.currentDebugger != nothing
UpdateDocumentLineStates(win32com_.gen_py.debugger.currentDebugger, self)
end
end

function _IsReadOnly(self::EditorDocumentBase)
return self.fileStat != nothing && (self.fileStat[1] & 128) == 0
end

function _UpdateUIForState(self::EditorDocumentBase)
#= Change the title to reflect the state of the document -
        eg ReadOnly, Dirty, etc
         =#
filename = GetPathName(self)
if !(filename)
return
end
try
ShowWindow(GetFirstView(self), win32con.SW_SHOW)
title = GetFileTitle(win32ui, filename)
catch exn
if exn isa win32ui.error
title = filename
end
end
if _IsReadOnly(self)
title = title * " (read-only)"
end
SetTitle(self, title)
end

function MakeDocumentWritable(self::EditorDocumentBase)::Int64
pretend_ss = 0
if !(self.scModuleName) && !(pretend_ss)
SetStatusText(win32ui, "Document is read-only, and no source-control system is configured")
MessageBeep(win32api)
return 0
end
msg = "Would you like to check this file out?"
defButton = win32con.MB_YESNO
if IsModified(self)
msg = msg * "\r\n\r\nALL CHANGES IN THE EDITOR WILL BE LOST"
defButton = win32con.MB_YESNO
end
if MessageBox(win32ui, msg, nothing, defButton) != win32con.IDYES
return 0
end
if pretend_ss != 0
println("We are only pretending to check it out!")
SetFileAttributes(win32api, GetPathName(self), win32con.FILE_ATTRIBUTE_NORMAL)
ReloadDocument(self)
return 1
end
if self.scModule === nothing
try
self.scModule = __import__(self.scModuleName)
for part in split(self.scModuleName, ".")[2:end]
self.scModule = getfield(self.scModule, :part)
end
catch exn
current_exceptions() != [] ? current_exceptions()[end] : nothing
println("Error loading source control module.")
return 0
end
end
if CheckoutFile(self.scModule, GetPathName(self))
ReloadDocument(self)
return 1
end
return 0
end

function CheckMakeDocumentWritable(self::EditorDocumentBase)::Int64
if _IsReadOnly(self)
return MakeDocumentWritable(self)
end
return 1
end

function SaveModified(self::EditorDocumentBase)
if IsModified(self)
frame = GetParentFrame(GetFirstView(self))
try
MDIActivate(frame)
AutoRestore(frame)
catch exn
println("Could not bring document to foreground")
end
end
return SaveModified(self._obj_)
end

import win32com_.gen_py.mfc.thread
import win32event
mutable struct FileWatchingThread <: AbstractFileWatchingThread
doc
adminEvent
stopEvent
watchEvent
hwnd

            FileWatchingThread(doc) = begin
                win32com_.gen_py.mfc.thread.WinThread.__init__(self)
                new(doc)
            end
end
function _DocumentStateChanged(self::FileWatchingThread)
SetEvent(win32event, self.adminEvent)
end

function RefreshEvent(self::FileWatchingThread)
self.hwnd = GetSafeHwnd(GetFirstView(self.doc))
if self.watchEvent != nothing
FindCloseChangeNotification(win32api, self.watchEvent)
self.watchEvent = nothing
end
path = GetPathName(self.doc)
if path
path = dirname(os.path, path)
end
if path
filter = (win32con.FILE_NOTIFY_CHANGE_FILE_NAME | win32con.FILE_NOTIFY_CHANGE_ATTRIBUTES) | win32con.FILE_NOTIFY_CHANGE_LAST_WRITE
try
self.watchEvent = FindFirstChangeNotification(win32api, path, 0, filter)
catch exn
 let exc = exn
if exc isa win32api.error
println("Can not watch file$(path)for changes -$(exc.strerror)")
end
end
end
end
end

function SignalStop(self::FileWatchingThread)
SetEvent(win32event, self.stopEvent)
end

function Run(self::FileWatchingThread)
while true
handles = [self.stopEvent, self.adminEvent]
if self.watchEvent != nothing
push!(handles, self.watchEvent)
end
rc = WaitForMultipleObjects(win32event, handles, 0, win32event.INFINITE)
if rc == win32event.WAIT_OBJECT_0
has_break = true
break;
elseif rc == (win32event.WAIT_OBJECT_0 + 1)
RefreshEvent(self)
else
PostMessage(win32api, self.hwnd, MSG_CHECK_EXTERNAL_FILE, 0, 0)
try
FindNextChangeNotification(win32api, self.watchEvent)
catch exn
 let exc = exn
if exc isa win32api.error
println("Can not watch file$(GetPathName(self.doc))for changes -$(exc.strerror)")
break;
end
end
end
end
end
self.doc = nothing
if self.watchEvent
FindCloseChangeNotification(win32api, self.watchEvent)
end
end
