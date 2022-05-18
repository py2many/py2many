using PyCall
win32ui = pyimport("win32ui")
import win32com_.gen_py.debugger
include("dbgcon.jl")
using win32com_.gen_py.mfc: dialog

abstract type AbstractDebuggerOptionsPropPage <: Abstractdialog.PropertyPage end
mutable struct DebuggerOptionsPropPage <: AbstractDebuggerOptionsPropPage
    options

    DebuggerOptionsPropPage() = begin
        dialog.PropertyPage.__init__(self, win32ui.IDD_PP_DEBUGGER)
        new()
    end
end
function OnInitDialog(self::DebuggerOptionsPropPage)
    options = LoadDebuggerOptions(dbgcon)
    self.options = LoadDebuggerOptions(dbgcon)
    AddDDX(self, win32ui.IDC_CHECK1, dbgcon.OPT_HIDE)
    self[dbgcon.OPT_STOP_EXCEPTIONS+1] = options[dbgcon.OPT_STOP_EXCEPTIONS+1]
    AddDDX(self, win32ui.IDC_CHECK2, dbgcon.OPT_STOP_EXCEPTIONS)
    self[dbgcon.OPT_HIDE+1] = options[dbgcon.OPT_HIDE+1]
    return OnInitDialog(dialog.PropertyPage)
end

function OnOK(self::DebuggerOptionsPropPage)::Int64
    UpdateData(self)
    dirty = 0
    for (key, val) in collect(items(self))
        if key ∈ self.options
            if self.options[key+1] != val
                self.options[key+1] = val
                dirty = 1
            end
        end
    end
    if dirty != 0
        SaveDebuggerOptions(dbgcon, self.options)
    end
    if win32com_.gen_py.debugger.currentDebugger != nothing
        win32com_.gen_py.debugger.currentDebugger.options = self.options
    end
    return 1
end
