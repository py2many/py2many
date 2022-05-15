module regedit
using PyCall
win32ui = pyimport("win32ui")
win32api = pyimport("win32api")
import win32con
import commctrl
using win32com_.gen_py.mfc: window, docview, dialog
include("hierlist.jl")
import regutil
import string
function SafeApply(fn, args, err_desc = "")::Int64
    try
        fn(args...)
        return 1
    catch exn
        let exc = exn
            if exc isa win32api.error
                msg = ("Error " + err_desc) * "\r\n\r\n" + exc.strerror
                MessageBox(win32ui, msg)
                return 0
            end
        end
    end
end

mutable struct SplitterFrame <: AbstractSplitterFrame
    images
    keysview::AbstractRegistryTreeView
    valuesview::AbstractRegistryValueView

    SplitterFrame() = begin
        window.MDIChildWnd.__init__(self)
        new()
    end
end
function OnCreateClient(self::SplitterFrame, cp, context)::Int64
    splitter = CreateSplitter(win32ui)
    doc = context.doc
    frame_rect = GetWindowRect(self)
    size = (frame_rect[3] - frame_rect[1], (frame_rect[4] - frame_rect[2]) ÷ 2)
    sub_size = (size[1] ÷ 3, size[2])
    CreateStatic(splitter, self, 1, 2)
    self.keysview = RegistryTreeView(doc)
    self.valuesview = RegistryValueView(doc)
    CreatePane(splitter, self.keysview, 0, 0, sub_size)
    CreatePane(splitter, self.valuesview, 0, 1, (0, 0))
    SetRowInfo(splitter, 0, size[2], 0)
    return 1
end

function OnItemDoubleClick(self::SplitterFrame, info, extra)::Int64
    hwndFrom, idFrom, code = info
    if idFrom == win32ui.AFX_IDW_PANE_FIRST
        return nothing
    elseif idFrom == (win32ui.AFX_IDW_PANE_FIRST + 1)
        item = SelectedItem(self.keysview)
        EditValue(self.valuesview, item)
        return 0
    else
        return nothing
    end
end

function PerformItemSelected(self::SplitterFrame, item)
    return UpdateForRegItem(self.valuesview, item)
end

function OnDestroy(self::SplitterFrame, msg)
    OnDestroy(window.MDIChildWnd, self)
    if self.images
        DeleteImageList(self.images)
        self.images = nothing
    end
end

abstract type AbstractSplitterFrame <: Abstractwindow.MDIChildWnd end
abstract type AbstractRegistryTreeView <: Abstractdocview.TreeView end
abstract type AbstractRegistryValueView <: Abstractdocview.ListView end
abstract type AbstractEditDialog <: Abstractdialog.Dialog end
abstract type AbstractRegTemplate <: Abstractdocview.DocTemplate end
abstract type AbstractRegDocument <: Abstractdocview.Document end
abstract type AbstractHLIRegistryKey <: Abstracthierlist.HierListItem end
mutable struct RegistryTreeView <: AbstractRegistryTreeView
    frame
    hierList
    OnItemRightClick
    OnAddKey
    OnAddValue
    OnDeleteKey
end
function OnInitialUpdate(self::RegistryTreeView)
    rc = OnInitialUpdate(self._obj_)
    self.frame = GetParent(GetParent(self))
    self.hierList = HierListWithItems(
        hierlist,
        GetHLIRoot(self),
        win32ui.IDB_HIERFOLDERS,
        win32ui.AFX_IDW_PANE_FIRST,
    )
    HierInit(self.hierList, self.frame, GetTreeCtrl(self))
    SetStyle(
        self.hierList,
        (commctrl.TVS_HASLINES | commctrl.TVS_LINESATROOT) | commctrl.TVS_HASBUTTONS,
    )
    self.hierList.PerformItemSelected = self.PerformItemSelected
    HookNotify(self.frame, self.frame.OnItemDoubleClick, commctrl.NM_DBLCLK)
    HookNotify(self.frame, self.OnItemRightClick, commctrl.NM_RCLICK)
end

function GetHLIRoot(self::RegistryTreeView)::HLIRegistryKey
    doc = GetDocument(self)
    regroot = doc.root
    subkey = doc.subkey
    return HLIRegistryKey(regroot, subkey, "Root")
end

function OnItemRightClick(self::RegistryTreeView, notify_data, extra)
    pt = ScreenToClient(self, GetCursorPos(win32api))
    flags, hItem = HitTest(self, pt)
    if hItem == 0 || (commctrl.TVHT_ONITEM & flags) == 0
        return nothing
    end
    Select(self, hItem, commctrl.TVGN_CARET)
    menu = CreatePopupMenu(win32ui)
    AppendMenu(menu, win32con.MF_STRING | win32con.MF_ENABLED, 1000, "Add Key")
    AppendMenu(menu, win32con.MF_STRING | win32con.MF_ENABLED, 1001, "Add Value")
    AppendMenu(menu, win32con.MF_STRING | win32con.MF_ENABLED, 1002, "Delete Key")
    HookCommand(self, self.OnAddKey, 1000)
    HookCommand(self, self.OnAddValue, 1001)
    HookCommand(self, self.OnDeleteKey, 1002)
    TrackPopupMenu(menu, GetCursorPos(win32api))
    return nothing
end

function OnDeleteKey(self::RegistryTreeView, command, code)
    hitem = GetSelectedItem(self.hierList)
    item = ItemFromHandle(self.hierList, hitem)
    msg = "Are you sure you wish to delete the key \'%s\'?" % (item.keyName,)
    id = MessageBox(win32ui, msg, nothing, win32con.MB_YESNO)
    if id != win32con.IDYES
        return
    end
    if SafeApply(
        win32api.RegDeleteKey,
        (item.keyRoot, item.keyName),
        "deleting registry key",
    ) != 0
        try
            hparent = GetParentItem(self, hitem)
        catch exn
            if exn isa win32ui.error
                hparent = nothing
            end
        end
        Refresh(self.hierList, hparent)
    end
end

function OnAddKey(self::RegistryTreeView, command, code)
    val = GetSimpleInput(dialog, "New key name", "", "Add new key")
    if val === nothing
        return
    end
    hitem = GetSelectedItem(self.hierList)
    item = ItemFromHandle(self.hierList, hitem)
    if SafeApply(win32api.RegCreateKey, (item.keyRoot, (item.keyName + "\\") + val)) != 0
        Refresh(self.hierList, hitem)
    end
end

function OnAddValue(self::RegistryTreeView, command, code)
    val = GetSimpleInput(dialog, "New value", "", "Add new value")
    if val === nothing
        return
    end
    hitem = GetSelectedItem(self.hierList)
    item = ItemFromHandle(self.hierList, hitem)
    if SafeApply(
        win32api.RegSetValue,
        (item.keyRoot, item.keyName, win32con.REG_SZ, val),
    ) != 0
        PerformItemSelected(self, item)
    end
end

function PerformItemSelected(self::RegistryTreeView, item)
    return PerformItemSelected(self.frame, item)
end

function SelectedItem(self::RegistryTreeView)
    return ItemFromHandle(self.hierList, GetSelectedItem(self.hierList))
end

function SearchSelectedItem(self::RegistryTreeView)
    handle = GetChildItem(self.hierList, 0)
    while true
        if GetItemState(self.hierList, handle, commctrl.TVIS_SELECTED)
            return ItemFromHandle(self.hierList, handle)
        end
        handle = GetNextSiblingItem(self.hierList, handle)
    end
end

mutable struct RegistryValueView <: AbstractRegistryValueView
    edit
    newvalue
    item
end
function OnInitialUpdate(self::RegistryValueView)
    hwnd = GetSafeHwnd(self._obj_)
    style = GetWindowLong(win32api, hwnd, win32con.GWL_STYLE)
    SetWindowLong(
        win32api,
        hwnd,
        win32con.GWL_STYLE,
        (style & ~(commctrl.LVS_TYPEMASK)) | commctrl.LVS_REPORT,
    )
    itemDetails = (commctrl.LVCFMT_LEFT, 100, "Name", 0)
    InsertColumn(self, 0, itemDetails)
    itemDetails = (commctrl.LVCFMT_LEFT, 500, "Data", 0)
    InsertColumn(self, 1, itemDetails)
end

function UpdateForRegItem(self::RegistryValueView, item)
    DeleteAllItems(self)
    hkey = RegOpenKey(win32api, item.keyRoot, item.keyName)
    try
        valNum = 0
        ret = []
        while true
            try
                res = RegEnumValue(win32api, hkey, valNum)
            catch exn
                if exn isa win32api.error
                    break
                end
            end
            name = res[1]
            if !(name)
                name = "(Default)"
            end
            InsertItem(self, valNum, name)
            SetItemText(self, valNum, 1, string(res[2]))
            valNum = valNum + 1
        end
    finally
        RegCloseKey(win32api, hkey)
    end
end

function EditValue(self::EditDialog, item)
    mutable struct EditDialog <: AbstractEditDialog
        edit
        newvalue
        item

        EditDialog(item) = begin
            dialog.Dialog.__init__(self, win32ui.IDD_LARGE_EDIT)
            new(item)
        end
    end
    function OnInitDialog(self::EditDialog)
        SetWindowText(self, "Enter new value")
        ShowWindow(GetDlgItem(self, win32con.IDCANCEL), win32con.SW_SHOW)
        self.edit = GetDlgItem(self, win32ui.IDC_EDIT1)
        style = GetWindowLong(win32api, GetSafeHwnd(self.edit), win32con.GWL_STYLE)
        style = style & ~(win32con.ES_WANTRETURN)
        SetWindowLong(win32api, GetSafeHwnd(self.edit), win32con.GWL_STYLE, style)
        SetWindowText(self.edit, string(self.item))
        SetSel(self.edit, -1)
        return OnInitDialog(dialog.Dialog)
    end

    function OnDestroy(self::EditDialog, msg)
        self.newvalue = GetWindowText(self.edit)
    end

    try
        index = GetNextItem(self, -1, commctrl.LVNI_SELECTED)
    catch exn
        if exn isa win32ui.error
            return
        end
    end
    if index == 0
        keyVal = ""
    else
        keyVal = GetItemText(self, index, 0)
    end
    try
        newVal = GetItemsCurrentValue(self, item, keyVal)
    catch exn
        let details = exn
            if details isa TypeError
                MessageBox(win32ui, details)
                return
            end
        end
    end
    d = EditDialog(newVal)
    if DoModal(d) == win32con.IDOK
        try
            SetItemsCurrentValue(self, item, keyVal, d.newvalue)
        catch exn
            let exc = exn
                if exc isa win32api.error
                    MessageBox(win32ui, "Error setting value\r\n\n%s" % exc.strerror)
                end
            end
        end
        UpdateForRegItem(self, item)
    end
end

function GetItemsCurrentValue(self::RegistryValueView, item, valueName)
    hkey = RegOpenKey(win32api, item.keyRoot, item.keyName)
    try
        val, type_ = RegQueryValueEx(win32api, hkey, valueName)
        if type_ != win32con.REG_SZ
            throw(TypeError("Only strings can be edited"))
        end
        return val
    finally
        RegCloseKey(win32api, hkey)
    end
end

function SetItemsCurrentValue(self::RegistryValueView, item, valueName, value)
    hkey = RegOpenKey(win32api, item.keyRoot, item.keyName, 0, win32con.KEY_SET_VALUE)
    try
        RegSetValueEx(win32api, hkey, valueName, 0, win32con.REG_SZ, value)
    finally
        RegCloseKey(win32api, hkey)
    end
end

mutable struct RegTemplate <: AbstractRegTemplate
    RegTemplate() = begin
        docview.DocTemplate.__init__(
            self,
            win32ui.IDR_PYTHONTYPE,
            nothing,
            SplitterFrame,
            nothing,
        )
        new()
    end
end
function OpenRegistryKey(self::RegTemplate, root = nothing, subkey = nothing)::RegDocument
    if root === nothing
        root = GetRootKey(regutil)
    end
    if subkey === nothing
        subkey = BuildDefaultPythonKey(regutil)
    end
    for doc in GetDocumentList(self)
        if doc.root == root && doc.subkey == subkey
            ActivateFrame(GetFirstView(doc))
            return doc
        end
    end
    doc = RegDocument(self, root, subkey)
    frame = CreateNewFrame(self, doc)
    OnNewDocument(doc)
    InitialUpdateFrame(self, frame, doc, 1)
    return doc
end

mutable struct RegDocument <: AbstractRegDocument
    root
    subkey

    RegDocument(template, root, subkey) = begin
        docview.Document.__init__(self, template)
        SetTitle("Registry Editor: " + subkey)
        new(template, root, subkey)
    end
end
function OnOpenDocument(self::RegDocument, name)::Int64
    throw(TypeError("This template can not open files"))
    return 0
end

mutable struct HLIRegistryKey <: AbstractHLIRegistryKey
    keyRoot
    keyName
    userName
    name
    __class__

    HLIRegistryKey(keyRoot, keyName, userName) = begin
        hierlist.HierListItem.__init__(self)
        new(keyRoot, keyName, userName)
    end
end
function __lt__(self::HLIRegistryKey, other)::Bool
    return self.name < other.name
end

function __eq__(self::HLIRegistryKey, other)
    return self.keyRoot == other.keyRoot &&
           self.keyName == other.keyName &&
           self.userName == other.userName
end

function __repr__(self::HLIRegistryKey)
    return "<%s with root=%s, key=%s>" %
           (self.__class__.__name__, self.keyRoot, self.keyName)
end

function GetText(self::HLIRegistryKey)
    return self.userName
end

function IsExpandable(self::HLIRegistryKey)::Int64
    return 1
end

function GetSubList(self::HLIRegistryKey)::Vector
    hkey = RegOpenKey(win32api, self.keyRoot, self.keyName)
    DoWaitCursor(win32ui, 1)
    try
        keyNum = 0
        ret = []
        while true
            try
                key = RegEnumKey(win32api, hkey, keyNum)
            catch exn
                if exn isa win32api.error
                    break
                end
            end
            push!(ret, HLIRegistryKey(self.keyRoot, (self.keyName + "\\") + key, key))
            keyNum = keyNum + 1
        end
    finally
        RegCloseKey(win32api, hkey)
        DoWaitCursor(win32ui, 0)
    end
    return ret
end

template = RegTemplate()
function EditRegistry(root = nothing, key = nothing)
    doc = OpenRegistryKey(template, root, key)
end

function main()
    EditRegistry()
end

main()
end
