using PyCall
win32ui = pyimport("win32ui")
using win32com_.gen_py.mfc: dialog
using win32com_.gen_py.framework: interact

import win32con
abstract type AbstractOptionsPropPage <: Abstractdialog.PropertyPage end
buttonControlMap = Dict(
    win32ui.IDC_BUTTON1 => win32ui.IDC_EDIT1,
    win32ui.IDC_BUTTON2 => win32ui.IDC_EDIT2,
    win32ui.IDC_BUTTON3 => win32ui.IDC_EDIT3,
)
mutable struct OptionsPropPage <: AbstractOptionsPropPage
    HandleCharFormatChange

    OptionsPropPage() = begin
        dialog.PropertyPage.__init__(self, win32ui.IDD_PP_IDE)
        AddDDX(win32ui.IDC_CHECK1, "bShowAtStartup")
        AddDDX(win32ui.IDC_CHECK2, "bDocking")
        AddDDX(win32ui.IDC_EDIT4, "MRUSize", "i")
        new()
    end
end
function OnInitDialog(self::OptionsPropPage)
    edit = GetDlgItem(self, win32ui.IDC_EDIT1)
    format = eval(
        GetProfileVal(
            win32ui,
            interact.sectionProfile,
            interact.STYLE_INTERACTIVE_PROMPT,
            string(interact.formatInput),
        ),
    )
    SetDefaultCharFormat(edit, format)
    SetWindowText(edit, "Input Text")
    edit = GetDlgItem(self, win32ui.IDC_EDIT2)
    format = eval(
        GetProfileVal(
            win32ui,
            interact.sectionProfile,
            interact.STYLE_INTERACTIVE_OUTPUT,
            string(interact.formatOutput),
        ),
    )
    SetDefaultCharFormat(edit, format)
    SetWindowText(edit, "Output Text")
    edit = GetDlgItem(self, win32ui.IDC_EDIT3)
    format = eval(
        GetProfileVal(
            win32ui,
            interact.sectionProfile,
            interact.STYLE_INTERACTIVE_ERROR,
            string(interact.formatOutputError),
        ),
    )
    SetDefaultCharFormat(edit, format)
    SetWindowText(edit, "Error Text")
    self["bShowAtStartup"] = LoadPreference(interact, "Show at startup", 1)
    self["bDocking"] = LoadPreference(interact, "Docking", 0)
    self["MRUSize"] = GetProfileVal(win32ui, "Settings", "Recent File List Size", 10)
    HookCommand(self, self.HandleCharFormatChange, win32ui.IDC_BUTTON1)
    HookCommand(self, self.HandleCharFormatChange, win32ui.IDC_BUTTON2)
    HookCommand(self, self.HandleCharFormatChange, win32ui.IDC_BUTTON3)
    spinner = GetDlgItem(self, win32ui.IDC_SPIN1)
    SetRange(spinner, 1, 16)
    return OnInitDialog(dialog.PropertyPage)
end

function HandleCharFormatChange(self::OptionsPropPage, id, code)::Int64
    if code == win32con.BN_CLICKED
        editId = get(buttonControlMap, id)
        @assert(editId != nothing)
        editControl = GetDlgItem(self, editId)
        existingFormat = GetDefaultCharFormat(editControl)
        flags = win32con.CF_SCREENFONTS
        d = CreateFontDialog(win32ui, existingFormat, flags, nothing, self)
        if DoModal(d) == win32con.IDOK
            cf = GetCharFormat(d)
            SetDefaultCharFormat(editControl, cf)
            SetModified(self, 1)
        end
        return 0
    end
end

function OnOK(self::OptionsPropPage)::Int64
    controlAttrs = [
        (win32ui.IDC_EDIT1, interact.STYLE_INTERACTIVE_PROMPT),
        (win32ui.IDC_EDIT2, interact.STYLE_INTERACTIVE_OUTPUT),
        (win32ui.IDC_EDIT3, interact.STYLE_INTERACTIVE_ERROR),
    ]
    for (id, key) in controlAttrs
        control = GetDlgItem(self, id)
        fmt = GetDefaultCharFormat(control)
        WriteProfileVal(win32ui, interact.sectionProfile, key, string(fmt))
    end
    SavePreference(interact, "Show at startup", self["bShowAtStartup"])
    SavePreference(interact, "Docking", self["bDocking"])
    WriteProfileVal(win32ui, "Settings", "Recent File List Size", self["MRUSize"])
    return 1
end

function ChangeFormat(self::OptionsPropPage, fmtAttribute, fmt)
    dlg = CreateFontDialog(win32ui, fmt)
    if DoModal(dlg) != win32con.IDOK
        return nothing
    end
    return GetCharFormat(dlg)
end

function OnFormatTitle(self::OptionsPropPage, command, code)
    fmt = GetFormat(self, interact.formatTitle)
    if fmt
        formatTitle = fmt
        SaveFontPreferences()
    end
end

function OnFormatInput(self::OptionsPropPage, command, code)
    global formatInput
    fmt = GetFormat(self, formatInput)
    if fmt
        formatInput = fmt
        SaveFontPreferences()
    end
end

function OnFormatOutput(self::OptionsPropPage, command, code)
    global formatOutput
    fmt = GetFormat(self, formatOutput)
    if fmt
        formatOutput = fmt
        SaveFontPreferences()
    end
end

function OnFormatError(self::OptionsPropPage, command, code)
    global formatOutputError
    fmt = GetFormat(self, formatOutputError)
    if fmt
        formatOutputError = fmt
        SaveFontPreferences()
    end
end
