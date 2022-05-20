using PyCall
pythoncom = pyimport("pythoncom")
win32ui = pyimport("win32ui")
win32api = pyimport("win32api")

import commctrl

using win32com_.gen_py.mfc: dialog
import win32com_.ext_modules.win32con as win32con
abstract type AbstractTLBrowserException <: AbstractException end
abstract type AbstractTypeBrowseDialog <: AbstractTypeBrowseDialog_Parent end
mutable struct TLBrowserException <: AbstractTLBrowserException
    #= TypeLib browser internal error =#

end

error = TLBrowserException
FRAMEDLG_STD = win32con.WS_CAPTION | win32con.WS_SYSMENU
SS_STD = win32con.WS_CHILD | win32con.WS_VISIBLE
BS_STD = SS_STD | win32con.WS_TABSTOP
ES_STD = BS_STD | win32con.WS_BORDER
LBS_STD =
    ((ES_STD | win32con.LBS_NOTIFY) | win32con.LBS_NOINTEGRALHEIGHT) | win32con.WS_VSCROLL
CBS_STD = (ES_STD | win32con.CBS_NOINTEGRALHEIGHT) | win32con.WS_VSCROLL
typekindmap = Dict(
    pythoncom.TKIND_ENUM => "Enumeration",
    pythoncom.TKIND_RECORD => "Record",
    pythoncom.TKIND_MODULE => "Module",
    pythoncom.TKIND_INTERFACE => "Interface",
    pythoncom.TKIND_DISPATCH => "Dispatch",
    pythoncom.TKIND_COCLASS => "CoClass",
    pythoncom.TKIND_ALIAS => "Alias",
    pythoncom.TKIND_UNION => "Union",
)
TypeBrowseDialog_Parent = dialog.Dialog
mutable struct TypeBrowseDialog <: AbstractTypeBrowseDialog
    #= Browse a type library =#
    OnFileOpen
    attr
    listview
    memberlb
    paramlb
    tlb
    typeinfo
    typelb
    IDC_LISTVIEW::Int64
    IDC_MEMBERLIST::Int64
    IDC_PARAMLIST::Int64
    IDC_TYPELIST::Int64
    typefile

    TypeBrowseDialog(
        typefile = nothing,
        IDC_LISTVIEW::Int64 = 1003,
        IDC_MEMBERLIST::Int64 = 1001,
        IDC_PARAMLIST::Int64 = 1002,
        IDC_TYPELIST::Int64 = 1000,
    ) = begin
        TypeBrowseDialog_Parent.__init__(self, GetTemplate())
        try
            if typefile
                tlb = pythoncom.LoadTypeLib(typefile)
            else
                tlb = nothing
            end
        catch exn
            if exn isa pythoncom.ole_error
                MessageBox("The file does not contain type information")
                tlb = nothing
            end
        end
        HookCommand(CmdTypeListbox, IDC_TYPELIST)
        HookCommand(CmdMemberListbox, IDC_MEMBERLIST)
        new(typefile, IDC_LISTVIEW, IDC_MEMBERLIST, IDC_PARAMLIST, IDC_TYPELIST)
    end
end
function OnAttachedObjectDeath(self::TypeBrowseDialog)
    self.tlb = nothing
    self.typeinfo = nothing
    self.attr = nothing
    return OnAttachedObjectDeath(TypeBrowseDialog_Parent)
end

function _SetupMenu(self::TypeBrowseDialog)
    menu = CreateMenu(win32ui)
    flags = win32con.MF_STRING | win32con.MF_ENABLED
    AppendMenu(menu, flags, win32ui.ID_FILE_OPEN, "&Open...")
    AppendMenu(menu, flags, win32con.IDCANCEL, "&Close")
    mainMenu = CreateMenu(win32ui)
    AppendMenu(mainMenu, flags | win32con.MF_POPUP, GetHandle(menu), "&File")
    SetMenu(self, mainMenu)
    HookCommand(self, self.OnFileOpen, win32ui.ID_FILE_OPEN)
end

function OnFileOpen(self::TypeBrowseDialog, id, code)
    openFlags = win32con.OFN_OVERWRITEPROMPT | win32con.OFN_FILEMUSTEXIST
    fspec = "Type Libraries (*.tlb, *.olb)|*.tlb;*.olb|OCX Files (*.ocx)|*.ocx|DLL\'s (*.dll)|*.dll|All Files (*.*)|*.*||"
    dlg = CreateFileDialog(win32ui, 1, nothing, nothing, openFlags, fspec)
    if DoModal(dlg) == win32con.IDOK
        try
            self.tlb = LoadTypeLib(pythoncom, GetPathName(dlg))
        catch exn
            if exn isa pythoncom.ole_error
                MessageBox(self, "The file does not contain type information")
                self.tlb = nothing
            end
        end
        _SetupTLB(self)
    end
end

function OnInitDialog(self::TypeBrowseDialog)
    _SetupMenu(self)
    self.typelb = GetDlgItem(self, self.IDC_TYPELIST)
    self.memberlb = GetDlgItem(self, self.IDC_MEMBERLIST)
    self.paramlb = GetDlgItem(self, self.IDC_PARAMLIST)
    self.listview = GetDlgItem(self, self.IDC_LISTVIEW)
    itemDetails = (commctrl.LVCFMT_LEFT, 100, "Item", 0)
    InsertColumn(self.listview, 0, itemDetails)
    itemDetails = (commctrl.LVCFMT_LEFT, 1024, "Details", 0)
    InsertColumn(self.listview, 1, itemDetails)
    if self.tlb === nothing
        OnFileOpen(self, nothing, nothing)
    else
        _SetupTLB(self)
    end
    return OnInitDialog(TypeBrowseDialog_Parent)
end

function _SetupTLB(self::TypeBrowseDialog)
    ResetContent(self.typelb)
    ResetContent(self.memberlb)
    ResetContent(self.paramlb)
    self.typeinfo = nothing
    self.attr = nothing
    if self.tlb === nothing
        return
    end
    n = GetTypeInfoCount(self.tlb)
    for i = 0:n-1
        AddString(self.typelb, GetDocumentation(self.tlb, i)[1])
    end
end

function _SetListviewTextItems(self::TypeBrowseDialog, items)
    DeleteAllItems(self.listview)
    index = -1
    for item in items
        index = InsertItem(self.listview, index + 1, item[1])
        data = item[2]
        if data === nothing
            data = ""
        end
        SetItemText(self.listview, index, 1, data)
    end
end

function SetupAllInfoTypes(self::TypeBrowseDialog)
    infos = append!(_GetMainInfoTypes(self), _GetMethodInfoTypes(self))
    _SetListviewTextItems(self, infos)
end

function _GetMainInfoTypes(self::TypeBrowseDialog)::Vector
    pos = GetCurSel(self.typelb)
    if pos < 0
        return []
    end
    docinfo = GetDocumentation(self.tlb, pos)
    infos = [("GUID", string(self.attr[1]))]
    push!(infos, ("Help File", docinfo[4]))
    push!(infos, ("Help Context", string(docinfo[3])))
    try
        push!(infos, ("Type Kind", typekindmap[GetTypeInfoType(self.tlb, pos)]))
    catch exn
        #= pass =#
    end
    info = GetTypeInfo(self.tlb, pos)
    attr = GetTypeAttr(info)
    push!(infos, ("Attributes", string(attr)))
    for j = 0:attr[9]-1
        flags = GetImplTypeFlags(info, j)
        refInfo = GetRefTypeInfo(info, GetRefTypeOfImplType(info, j))
        doc = GetDocumentation(refInfo, -1)
        attr = GetTypeAttr(refInfo)
        typeKind = attr[6]
        typeFlags = attr[12]
        desc = doc[1]
        desc =
            desc +
            (", Flags=0x%x, typeKind=0x%x, typeFlags=0x%x" % (flags, typeKind, typeFlags))
        if flags & pythoncom.IMPLTYPEFLAG_FSOURCE
            desc = desc * "(Source)"
        end
        push!(infos, ("Implements", desc))
    end
    return infos
end

function _GetMethodInfoTypes(self::TypeBrowseDialog)::Vector
    pos = GetCurSel(self.memberlb)
    if pos < 0
        return []
    end
    realPos, isMethod = _GetRealMemberPos(self, pos)
    ret = []
    if isMethod
        funcDesc = GetFuncDesc(self.typeinfo, realPos)
        id = funcDesc[1]
        push!(ret, ("Func Desc", string(funcDesc)))
    else
        id = GetVarDesc(self.typeinfo, realPos)[1]
    end
    docinfo = GetDocumentation(self.typeinfo, id)
    push!(ret, ("Help String", docinfo[2]))
    push!(ret, ("Help Context", string(docinfo[3])))
    return ret
end

function CmdTypeListbox(self::TypeBrowseDialog, id, code)::Int64
    if code == win32con.LBN_SELCHANGE
        pos = GetCurSel(self.typelb)
        if pos >= 0
            ResetContent(self.memberlb)
            self.typeinfo = GetTypeInfo(self.tlb, pos)
            self.attr = GetTypeAttr(self.typeinfo)
            for i = 0:self.attr[8]-1
                id = GetVarDesc(self.typeinfo, i)[1]
                AddString(self.memberlb, GetNames(self.typeinfo, id)[1])
            end
            for i = 0:self.attr[7]-1
                id = GetFuncDesc(self.typeinfo, i)[1]
                AddString(self.memberlb, GetNames(self.typeinfo, id)[1])
            end
            SetupAllInfoTypes(self)
        end
        return 1
    end
end

function _GetRealMemberPos(self::TypeBrowseDialog, pos)
    pos = GetCurSel(self.memberlb)
    if pos >= self.attr[8]
        return (pos - self.attr[8], 1)
    elseif pos >= 0
        return (pos, 0)
    else
        throw(error("The position is not valid"))
    end
end

function CmdMemberListbox(self::TypeBrowseDialog, id, code)::Int64
    if code == win32con.LBN_SELCHANGE
        ResetContent(self.paramlb)
        pos = GetCurSel(self.memberlb)
        realPos, isMethod = _GetRealMemberPos(self, pos)
        if isMethod
            id = GetFuncDesc(self.typeinfo, realPos)[1]
            names = GetNames(self.typeinfo, id)
            for i = 0:length(names)-1
                if i > 0
                    AddString(self.paramlb, names[i+1])
                end
            end
        end
        SetupAllInfoTypes(self)
        return 1
    end
end

function GetTemplate(self::TypeBrowseDialog)
    #= Return the template used to create this dialog =#
    w = 272
    h = 192
    style =
        ((FRAMEDLG_STD | win32con.WS_VISIBLE) | win32con.DS_SETFONT) |
        win32con.WS_MINIMIZEBOX
    template = [["Type Library Browser", (0, 0, w, h), style, nothing, (8, "Helv")]]
    push!(template, [130, "&Type", -1, (10, 10, 62, 9), SS_STD | win32con.SS_LEFT])
    push!(template, [131, nothing, self.IDC_TYPELIST, (10, 20, 80, 80), LBS_STD])
    push!(template, [130, "&Members", -1, (100, 10, 62, 9), SS_STD | win32con.SS_LEFT])
    push!(template, [131, nothing, self.IDC_MEMBERLIST, (100, 20, 80, 80), LBS_STD])
    push!(template, [130, "&Parameters", -1, (190, 10, 62, 9), SS_STD | win32con.SS_LEFT])
    push!(template, [131, nothing, self.IDC_PARAMLIST, (190, 20, 75, 80), LBS_STD])
    lvStyle =
        (
            (
                ((SS_STD | commctrl.LVS_REPORT) | commctrl.LVS_AUTOARRANGE) |
                commctrl.LVS_ALIGNLEFT
            ) | win32con.WS_BORDER
        ) | win32con.WS_TABSTOP
    push!(template, ["SysListView32", "", self.IDC_LISTVIEW, (10, 110, 255, 65), lvStyle])
    return template
end

if abspath(PROGRAM_FILE) == @__FILE__
    fname = nothing
    try
        fname = append!([PROGRAM_FILE], ARGS)[2]
    catch exn
        #= pass =#
    end
    dlg = TypeBrowseDialog(fname)
    try
        GetConsoleTitle(win32api)
        DoModal(dlg)
    catch exn
        CreateWindow(dlg, GetMainFrame(win32ui))
    end
end
