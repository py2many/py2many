using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
using win32com_.gen_py.mfc: dialog
import win32con
import commctrl
abstract type AbstractListDialog <: Abstractdialog.Dialog end
abstract type AbstractListsDialog <: AbstractListDialog end
mutable struct ListDialog <: AbstractListDialog
    items
    selecteditem
    itemsControl
    butOK
    butCancel

    ListDialog(title, list) = begin
        dialog.Dialog.__init__(self, _maketemplate(title))
        HookMessage(on_size, win32con.WM_SIZE)
        HookNotify(OnListItemChange, commctrl.LVN_ITEMCHANGED)
        HookCommand(OnListClick, win32ui.IDC_LIST1)
        new(title, list)
    end
end
function _maketemplate(self::ListDialog, title)
    style = (win32con.WS_DLGFRAME | win32con.WS_SYSMENU) | win32con.WS_VISIBLE
    ls =
        ((win32con.WS_CHILD | win32con.WS_VISIBLE) | commctrl.LVS_ALIGNLEFT) |
        commctrl.LVS_REPORT
    bs = win32con.WS_CHILD | win32con.WS_VISIBLE
    return [
        [title, (0, 0, 200, 200), style, nothing, (8, "MS Sans Serif")],
        ["SysListView32", nothing, win32ui.IDC_LIST1, (0, 0, 200, 200), ls],
        [128, "OK", win32con.IDOK, (10, 0, 50, 14), bs | win32con.BS_DEFPUSHBUTTON],
        [128, "Cancel", win32con.IDCANCEL, (0, 0, 50, 14), bs],
    ]
end

function FillList(self::ListDialog)
    size = GetWindowRect(self)
    width = (size[3] - size[1]) - 10
    itemDetails = (commctrl.LVCFMT_LEFT, width, "Item", 0)
    InsertColumn(self.itemsControl, 0, itemDetails)
    index = 0
    for item in self.items
        index = InsertItem(self.itemsControl, index + 1, string(item), 0)
    end
end

function OnListClick(self::ListDialog, id, code)::Int64
    if code == commctrl.NM_DBLCLK
        EndDialog(self, win32con.IDOK)
    end
    return 1
end

function OnListItemChange(self::ListDialog, std, extra)
    (hwndFrom, idFrom, code), (itemNotify, sub, newState, oldState, change, point, lparam) =
        (std, extra)
    oldSel = (oldState & commctrl.LVIS_SELECTED) != 0
    newSel = (newState & commctrl.LVIS_SELECTED) != 0
    if oldSel != newSel
        try
            self.selecteditem = itemNotify
            EnableWindow(self.butOK, 1)
        catch exn
            if exn isa win32ui.error
                self.selecteditem = nothing
            end
        end
    end
end

function OnInitDialog(self::ListDialog)
    rc = OnInitDialog(dialog.Dialog)
    self.itemsControl = GetDlgItem(self, win32ui.IDC_LIST1)
    self.butOK = GetDlgItem(self, win32con.IDOK)
    self.butCancel = GetDlgItem(self, win32con.IDCANCEL)
    FillList(self)
    size = GetWindowRect(self)
    LayoutControls(self, size[3] - size[1], size[4] - size[2])
    EnableWindow(self.butOK, 0)
    return rc
end

function LayoutControls(self::ListDialog, w, h)
    MoveWindow(self.itemsControl, (0, 0, w, h - 30))
    MoveWindow(self.butCancel, (10, h - 24, 60, h - 4))
    MoveWindow(self.butOK, (w - 60, h - 24, w - 10, h - 4))
end

function on_size(self::ListDialog, params)
    lparam = params[4]
    w = LOWORD(win32api, lparam)
    h = HIWORD(win32api, lparam)
    LayoutControls(self, w, h)
end

mutable struct ListsDialog <: AbstractListsDialog
    colHeadings
    items

    ListsDialog(title, list, colHeadings = ["Item"]) = begin
        ListDialog(title, list)
        new(title, list, colHeadings)
    end
end
function FillList(self::ListsDialog)
    index = 0
    size = GetWindowRect(self)
    width = ((size[3] - size[1]) - 10) - GetSystemMetrics(win32api, win32con.SM_CXVSCROLL)
    numCols = length(self.colHeadings)
    for col in self.colHeadings
        itemDetails = (commctrl.LVCFMT_LEFT, Int(floor(width / numCols)), col, 0)
        InsertColumn(self.itemsControl, index, itemDetails)
        index = index + 1
    end
    index = 0
    for items in self.items
        index = InsertItem(self.itemsControl, index + 1, string(items[1]), 0)
        for itemno = 1:numCols-1
            item = items[itemno+1]
            SetItemText(self.itemsControl, index, itemno, string(item))
        end
    end
end

function SelectFromList(title, lst)
    dlg = ListDialog(title, lst)
    if DoModal(dlg) == win32con.IDOK
        return dlg.selecteditem
    else
        return nothing
    end
end

function SelectFromLists(title, lists, headings)
    dlg = ListsDialog(title, lists, headings)
    if DoModal(dlg) == win32con.IDOK
        return dlg.selecteditem
    else
        return nothing
    end
end

function test()
    println(
        SelectFromLists(
            "Multi-List",
            [("1", 1, "a"), ("2", 2, "b"), ("3", 3, "c")],
            ["Col 1", "Col 2"],
        ),
    )
end

if abspath(PROGRAM_FILE) == @__FILE__
    test()
end
