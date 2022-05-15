module configui
using PyCall
win32ui = pyimport("win32ui")
win32api = pyimport("win32api")
include("control.jl")

import win32com_.gen_py.scintilla.view
using win32com_.gen_py.mfc: dialog

import win32con

import copy
import string
include("scintillacon.jl")
using win32con: CLR_INVALID
abstract type AbstractScintillaFormatPropertyPage <: Abstractdialog.PropertyPage end
paletteVGA = (
    ("Black", RGB(win32api, 0, 0, 0)),
    ("Navy", RGB(win32api, 0, 0, 128)),
    ("Green", RGB(win32api, 0, 128, 0)),
    ("Cyan", RGB(win32api, 0, 128, 128)),
    ("Maroon", RGB(win32api, 128, 0, 0)),
    ("Purple", RGB(win32api, 128, 0, 128)),
    ("Olive", RGB(win32api, 128, 128, 0)),
    ("Gray", RGB(win32api, 128, 128, 128)),
    ("Silver", RGB(win32api, 192, 192, 192)),
    ("Blue", RGB(win32api, 0, 0, 255)),
    ("Lime", RGB(win32api, 0, 255, 0)),
    ("Aqua", RGB(win32api, 0, 255, 255)),
    ("Red", RGB(win32api, 255, 0, 0)),
    ("Fuchsia", RGB(win32api, 255, 0, 255)),
    ("Yellow", RGB(win32api, 255, 255, 0)),
    ("White", RGB(win32api, 255, 255, 255)),
    ("DarkGrey", RGB(win32api, 64, 64, 64)),
    ("PurpleBlue", RGB(win32api, 64, 64, 192)),
    ("DarkGreen", RGB(win32api, 0, 96, 0)),
    ("DarkOlive", RGB(win32api, 128, 128, 64)),
    ("MediumBlue", RGB(win32api, 0, 0, 192)),
    ("DarkNavy", RGB(win32api, 0, 0, 96)),
    ("Magenta", RGB(win32api, 96, 0, 96)),
    ("OffWhite", RGB(win32api, 255, 255, 220)),
    ("LightPurple", RGB(win32api, 220, 220, 255)),
    ("<Default>", win32con.CLR_INVALID),
)
mutable struct ScintillaFormatPropertyPage <: AbstractScintillaFormatPropertyPage
    OnBraceMatch
    OnButDefaultFixedFont
    OnButDefaultPropFont
    OnButFixedOrDefault
    OnButThisBackground
    OnButThisFont
    OnButUseDefaultBackground
    OnButUseDefaultFont
    OnEsc
    OnListCommand
    OnStyleUIChanged
    butIsDefault
    butIsDefaultBackground
    cbo
    cboBoldItalic
    listbox
    pos_bbad::Int64
    pos_bend::Int64
    pos_bstart::Int64
    scintilla
    scintillaClass
    styles
    caption::Int64

    ScintillaFormatPropertyPage(scintillaClass = nothing, caption = 0) = begin
        dialog.PropertyPage.__init__(self, win32ui.IDD_PP_FORMAT, caption = caption)
        new(scintillaClass, caption)
    end
end
function OnInitDialog(self::ScintillaFormatPropertyPage)
    try
        if self.scintillaClass === nothing
            sc = control.CScintillaEdit
        else
            sc = self.scintillaClass
        end
        self.scintilla = sc()
        style = (win32con.WS_CHILD | win32con.WS_VISIBLE) | win32con.ES_MULTILINE
        rect = MapDialogRect(self, (5, 5, 120, 75))
        CreateWindow(self.scintilla, style, rect, self, 111)
        HookNotify(self, self.OnBraceMatch, scintillacon.SCN_CHECKBRACE)
        HookKeyStroke(self.scintilla, self.OnEsc, 27)
        SCISetViewWS(self.scintilla, 1)
        self.pos_bstart = 0
        self.pos_bend = 0
        self.pos_bbad = 0
        colorizer = _GetColorizer(self.scintilla)
        text = GetSampleText(colorizer)
        items = split(text, "|", 2)
        pos = length(items[1])
        SCIAddText(self.scintilla, join(items, ""))
        SetSel(self.scintilla, pos, pos)
        ApplyFormattingStyles(self.scintilla)
        self.styles = _GetColorizer(self.scintilla).styles
        self.cbo = GetDlgItem(self, win32ui.IDC_COMBO1)
        for c in paletteVGA
            AddString(self.cbo, c[1])
        end
        self.cboBoldItalic = GetDlgItem(self, win32ui.IDC_COMBO2)
        for item in ["Bold Italic", "Bold", "Italic", "Regular"]
            InsertString(self.cboBoldItalic, 0, item)
        end
        self.butIsDefault = GetDlgItem(self, win32ui.IDC_CHECK1)
        self.butIsDefaultBackground = GetDlgItem(self, win32ui.IDC_CHECK2)
        self.listbox = GetDlgItem(self, win32ui.IDC_LIST1)
        HookCommand(self, self.OnListCommand, win32ui.IDC_LIST1)
        names = collect(keys(self.styles))
        sort(names)
        for name in names
            if self.styles[name+1].aliased === nothing
                AddString(self.listbox, name)
            end
        end
        SetCurSel(self.listbox, 0)
        idc = win32ui.IDC_RADIO1
        if !(_GetColorizer(self.scintilla).bUseFixed)
            idc = win32ui.IDC_RADIO2
        end
        SetCheck(GetDlgItem(self, idc), 1)
        UpdateUIForStyle(self, self.styles[names[1]+1])
        HookFormatter(self.scintilla, self)
        HookCommand(self, self.OnButDefaultFixedFont, win32ui.IDC_BUTTON1)
        HookCommand(self, self.OnButDefaultPropFont, win32ui.IDC_BUTTON2)
        HookCommand(self, self.OnButThisFont, win32ui.IDC_BUTTON3)
        HookCommand(self, self.OnButUseDefaultFont, win32ui.IDC_CHECK1)
        HookCommand(self, self.OnButThisBackground, win32ui.IDC_BUTTON4)
        HookCommand(self, self.OnButUseDefaultBackground, win32ui.IDC_CHECK2)
        HookCommand(self, self.OnStyleUIChanged, win32ui.IDC_COMBO1)
        HookCommand(self, self.OnStyleUIChanged, win32ui.IDC_COMBO2)
        HookCommand(self, self.OnButFixedOrDefault, win32ui.IDC_RADIO1)
        HookCommand(self, self.OnButFixedOrDefault, win32ui.IDC_RADIO2)
    catch exn
        current_exceptions() != [] ? current_exceptions()[end] : nothing
    end
end

function OnEsc(self::ScintillaFormatPropertyPage, ch)
    EndDialog(GetParent(self), win32con.IDCANCEL)
end

function OnBraceMatch(self::ScintillaFormatPropertyPage, std, extra)
    DoBraceMatch(win32com_.gen_py.scintilla.view, self.scintilla)
end

function GetSelectedStyle(self::ScintillaFormatPropertyPage)
    return self.styles[GetText(self.listbox, GetCurSel(self.listbox))+1]
end

function _DoButDefaultFont(self::ScintillaFormatPropertyPage, extra_flags, attr)
    baseFormat = getattr(_GetColorizer(self.scintilla), attr)
    flags =
        ((extra_flags | win32con.CF_SCREENFONTS) | win32con.CF_EFFECTS) |
        win32con.CF_FORCEFONTEXIST
    d = CreateFontDialog(win32ui, baseFormat, flags, nothing, self)
    if DoModal(d) == win32con.IDOK
        setattr(_GetColorizer(self.scintilla), attr, GetCharFormat(d))
        OnStyleUIChanged(self, 0, win32con.BN_CLICKED)
    end
end

function OnButDefaultFixedFont(self::ScintillaFormatPropertyPage, id, code)::Int64
    if code == win32con.BN_CLICKED
        _DoButDefaultFont(self, win32con.CF_FIXEDPITCHONLY, "baseFormatFixed")
        return 1
    end
end

function OnButDefaultPropFont(self::ScintillaFormatPropertyPage, id, code)::Int64
    if code == win32con.BN_CLICKED
        _DoButDefaultFont(self, win32con.CF_SCALABLEONLY, "baseFormatProp")
        return 1
    end
end

function OnButFixedOrDefault(self::ScintillaFormatPropertyPage, id, code)::Int64
    if code == win32con.BN_CLICKED
        bUseFixed = id == win32ui.IDC_RADIO1
        GetCheck(GetDlgItem(self, win32ui.IDC_RADIO1)) != 0
        _GetColorizer(self.scintilla).bUseFixed = bUseFixed
        ApplyFormattingStyles(self.scintilla, 0)
        return 1
    end
end

function OnButThisFont(self::ScintillaFormatPropertyPage, id, code)::Int64
    if code == win32con.BN_CLICKED
        flags = (win32con.CF_SCREENFONTS | win32con.CF_EFFECTS) | win32con.CF_FORCEFONTEXIST
        style = GetSelectedStyle(self)
        def_format = GetDefaultFormat(_GetColorizer(self.scintilla))
        format = GetCompleteFormat(style, def_format)
        d = CreateFontDialog(win32ui, format, flags, nothing, self)
        if DoModal(d) == win32con.IDOK
            style = GetCharFormat(d)
            ApplyFormattingStyles(self.scintilla, 0)
        end
        return 1
    end
end

function OnButUseDefaultFont(self::ScintillaFormatPropertyPage, id, code)
    if code == win32con.BN_CLICKED
        isDef = GetCheck(self.butIsDefault)
        EnableWindow(GetDlgItem(self, win32ui.IDC_BUTTON3), !(isDef))
        if isDef
            style = GetSelectedStyle(self)
            ForceAgainstDefault(style)
            UpdateUIForStyle(self, style)
            ApplyFormattingStyles(self.scintilla, 0)
        else
            #= pass =#
        end
    end
end

function OnButThisBackground(self::ScintillaFormatPropertyPage, id, code)::Int64
    if code == win32con.BN_CLICKED
        style = GetSelectedStyle(self)
        bg = RGB(win32api, 255, 255, 255)
        if style.background != CLR_INVALID
            bg = style.background
        end
        d = CreateColorDialog(win32ui, bg, 0, self)
        if DoModal(d) == win32con.IDOK
            style.background = GetColor(d)
            ApplyFormattingStyles(self.scintilla, 0)
        end
        return 1
    end
end

function OnButUseDefaultBackground(self::ScintillaFormatPropertyPage, id, code)
    if code == win32con.BN_CLICKED
        isDef = GetCheck(self.butIsDefaultBackground)
        EnableWindow(GetDlgItem(self, win32ui.IDC_BUTTON4), !(isDef))
        if isDef
            style = GetSelectedStyle(self)
            style.background = style.default_background
            UpdateUIForStyle(self, style)
            ApplyFormattingStyles(self.scintilla, 0)
        else
            #= pass =#
        end
    end
end

function OnListCommand(self::ScintillaFormatPropertyPage, id, code)::Int64
    if code == win32con.LBN_SELCHANGE
        style = GetSelectedStyle(self)
        UpdateUIForStyle(self, style)
    end
    return 1
end

function UpdateUIForStyle(self::ScintillaFormatPropertyPage, style)
    format = style
    sel = 0
    for c in paletteVGA
        if format[5] == c[2]
            break
        end
        sel = sel + 1
    end
    SetCurSel(self.cbo, sel)
    SetCheck(self.butIsDefault, IsBasedOnDefault(style))
    EnableWindow(GetDlgItem(self, win32ui.IDC_BUTTON3), !IsBasedOnDefault(style))
    SetCheck(self.butIsDefaultBackground, style.background == style.default_background)
    EnableWindow(
        GetDlgItem(self, win32ui.IDC_BUTTON4),
        style.background != style.default_background,
    )
    bold = (format[2] & win32con.CFE_BOLD) != 0
    italic = (format[2] & win32con.CFE_ITALIC) != 0
    SetCurSel(self.cboBoldItalic, bold * 2 + italic)
end

function OnStyleUIChanged(self::ScintillaFormatPropertyPage, id, code)::Int64
    if code in [win32con.BN_CLICKED, win32con.CBN_SELCHANGE]
        style = GetSelectedStyle(self)
        ApplyUIFormatToStyle(self, style)
        ApplyFormattingStyles(self.scintilla, 0)
        return 0
    end
    return 1
end

function ApplyUIFormatToStyle(self::ScintillaFormatPropertyPage, style)
    format = style
    color = paletteVGA[GetCurSel(self.cbo)+1]
    effect = 0
    sel = GetCurSel(self.cboBoldItalic)
    if sel == 0
        effect = 0
    elseif sel == 1
        effect = win32con.CFE_ITALIC
    elseif sel == 2
        effect = win32con.CFE_BOLD
    else
        effect = win32con.CFE_BOLD | win32con.CFE_ITALIC
    end
    maskFlags = ((format[1] | win32con.CFM_COLOR) | win32con.CFM_BOLD) | win32con.CFM_ITALIC
    style = (maskFlags, effect, style[3], style[4], color[2]) + style[6:end]
end

function OnOK(self::ScintillaFormatPropertyPage)::Int64
    SavePreferences(_GetColorizer(self.scintilla))
    return 1
end

function test()
    page = ColorEditorPropertyPage()
    sheet = PropertySheet(win32com_.gen_py.mfc.dialog, "Test")
    AddPage(sheet, page)
    CreateWindow(sheet)
end

end
