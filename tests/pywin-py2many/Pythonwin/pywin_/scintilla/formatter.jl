module formatter
using PyCall
win32ui = pyimport("win32ui")
win32api = pyimport("win32api")
import win32traceutil
import win32trace

import win32con
import winerror
import string

include("scintillacon.jl")
WM_KICKIDLE = 874
using win32con: CLR_INVALID
abstract type AbstractStyle end
abstract type AbstractFormatterBase end
abstract type AbstractFormatter <: AbstractFormatterBase end
abstract type AbstractPythonSourceFormatter <: AbstractFormatter end
abstract type AbstractBuiltinSourceFormatter <: AbstractFormatterBase end
abstract type AbstractBuiltinPythonSourceFormatter <: AbstractBuiltinSourceFormatter end
debugging = 0
if debugging != 0
    function trace()
        write(win32trace, join(map(str, args), " ") + "\n")
    end

else
    trace = () -> nothing
end
mutable struct Style <: AbstractStyle
    #= Represents a single format =#
    name
    background
    default_background
    aliased
    format
    stylenum

    Style(name, format, background = CLR_INVALID) = begin
        if type_(format) == type_("")
            aliased = format
            format = nothing
        else
            format = format
            aliased = nothing
        end
        new(name, format, background)
    end
end
function IsBasedOnDefault(self::Style)::Bool
    return length(self.format) == 5
end

function NormalizeAgainstDefault(self::Style, defaultFormat)::Int64
    if IsBasedOnDefault(self)
        return 0
    end
    bIsDefault = self.format[8] == defaultFormat[8] && self.format[3] == defaultFormat[3]
    if bIsDefault
        ForceAgainstDefault(self)
    end
    return bIsDefault
end

function ForceAgainstDefault(self::Style)
    self.format = self.format[begin:5]
end

function GetCompleteFormat(self::Style, defaultFormat)::Tuple
    if length(self.format) == 5
        fmt = self.format + defaultFormat[6:end]
    else
        fmt = self.format
    end
    flags =
        (
            (
                ((win32con.CFM_BOLD | win32con.CFM_CHARSET) | win32con.CFM_COLOR) |
                win32con.CFM_FACE
            ) | win32con.CFM_ITALIC
        ) | win32con.CFM_SIZE
    return (flags,) + fmt[2:end]
end

mutable struct FormatterBase <: AbstractFormatterBase
    scintilla
    baseFormatFixed::Tuple
    baseFormatProp::Tuple
    bUseFixed::Int64
    styles::Dict
    styles_by_id::Dict
    string_style_names

    FormatterBase(scintilla) = begin
        SetStyles()
        new(scintilla)
    end
end
function HookFormatter(self::FormatterBase, parent = nothing)
    throw(NotImplementedError())
end

function GetStringStyle(self::FormatterBase, pos)::Dict
    try
        style = self.styles_by_id[SCIGetStyleAt(self.scintilla, pos)]
    catch exn
        if exn isa KeyError
            return nothing
        end
    end
    if style.name in self.string_style_names
        return style
    end
    return nothing
end

function RegisterStyle(self::FormatterBase, style, stylenum)
    @assert(stylenum != nothing)
    @assert(style.stylenum === nothing)
    @assert(stylenum ∉ self.styles)
    style.stylenum = stylenum
    self.styles[style.name] = style
    self.styles_by_id[stylenum] = style
end

function SetStyles(self::FormatterBase)
    throw(NotImplementedError())
end

function GetSampleText(self::FormatterBase)::String
    return "Sample Text for the Format Dialog"
end

function GetDefaultFormat(self::FormatterBase)::Tuple
    if self.bUseFixed != 0
        return self.baseFormatFixed
    end
    return self.baseFormatProp
end

function _ReformatStyle(self::FormatterBase, style)
    if style.name == STYLE_SELECTION
        clr = style.background
        SendScintilla(self.scintilla, scintillacon.SCI_SETSELBACK, true, clr)
        return
    end
    @assert(style.stylenum != nothing)
    scintilla = self.scintilla
    stylenum = style.stylenum
    if style.aliased != nothing
        style = self.styles[style.aliased]
    end
    f = style
    if IsBasedOnDefault(style)
        baseFormat = GetDefaultFormat(self)
    else
        baseFormat = f
    end
    SCIStyleSetFore(scintilla, stylenum, f[5])
    SCIStyleSetFont(scintilla, stylenum, baseFormat[8], baseFormat[6])
    if f[2] & 1
        SCIStyleSetBold(scintilla, stylenum, 1)
    else
        SCIStyleSetBold(scintilla, stylenum, 0)
    end
    if f[2] & 2
        SCIStyleSetItalic(scintilla, stylenum, 1)
    else
        SCIStyleSetItalic(scintilla, stylenum, 0)
    end
    SCIStyleSetSize(scintilla, stylenum, Int(baseFormat[3] / 20))
    SCIStyleSetEOLFilled(scintilla, stylenum, 1)
    bg = style.background
    if bg == CLR_INVALID
        bg = self.styles[STYLE_DEFAULT].background
    end
    if bg == CLR_INVALID
        bg = GetSysColor(win32api, win32con.COLOR_WINDOW)
    end
    SCIStyleSetBack(scintilla, stylenum, bg)
end

function GetStyleByNum(self::FormatterBase, stylenum)::Dict
    return self.styles_by_id[stylenum]
end

function ApplyFormattingStyles(self::FormatterBase, bReload = 1)
    if bReload
        LoadPreferences(self)
    end
    baseFormat = GetDefaultFormat(self)
    defaultStyle = Style("default", baseFormat)
    defaultStyle.stylenum = scintillacon.STYLE_DEFAULT
    _ReformatStyle(self, defaultStyle)
    for style in collect(values(self.styles))
        if style.aliased === nothing
            NormalizeAgainstDefault(style, baseFormat)
        end
        _ReformatStyle(self, style)
    end
    InvalidateRect(self.scintilla)
end

function LoadPreferences(self::FormatterBase)
    self.baseFormatFixed =
        eval(LoadPreference(self, "Base Format Fixed", string(self.baseFormatFixed)))
    self.baseFormatProp =
        eval(LoadPreference(self, "Base Format Proportional", string(self.baseFormatProp)))
    self.bUseFixed = parse(Int, LoadPreference(self, "Use Fixed", 1))
    for style in collect(values(self.styles))
        new = LoadPreference(self, style.name, string(style))
        try
            style = eval(new)
        catch exn
            println("Error loading style data for", style.name)
        end
        style.background = parse(
            Int,
            LoadPreference(self, style.name + " background", style.default_background),
        )
    end
end

function LoadPreference(self::FormatterBase, name, default)
    return GetProfileVal(win32ui, "Format", name, default)
end

function SavePreferences(self::FormatterBase)
    SavePreference(self, "Base Format Fixed", string(self.baseFormatFixed))
    SavePreference(self, "Base Format Proportional", string(self.baseFormatProp))
    SavePreference(self, "Use Fixed", self.bUseFixed)
    for style in collect(values(self.styles))
        if style.aliased === nothing
            SavePreference(self, style.name, string(style))
            bg_name = style.name + " background"
            SavePreference(self, bg_name, style.background)
        end
    end
end

function SavePreference(self::FormatterBase, name, value)
    WriteProfileVal(win32ui, "Format", name, value)
end

mutable struct Formatter <: AbstractFormatter
    bCompleteWhileIdle::Int64
    bHaveIdleHandler::Int64
    nextstylenum::Int64
    style_buffer
    OnStyleNeeded
    DoMoreColoring

    Formatter(scintilla) = begin
        FormatterBase(scintilla)
        new(scintilla)
    end
end
function HookFormatter(self::Formatter, parent = nothing)
    if parent === nothing
        parent = GetParent(self.scintilla)
    end
    HookNotify(parent, self.OnStyleNeeded, scintillacon.SCN_STYLENEEDED)
end

function OnStyleNeeded(self::Formatter, std, extra)
    notify = SCIUnpackNotifyMessage(self.scintilla, extra)
    endStyledChar = SendScintilla(self.scintilla, scintillacon.SCI_GETENDSTYLED)
    lineEndStyled = LineFromChar(self.scintilla, endStyledChar)
    endStyled = LineIndex(self.scintilla, lineEndStyled)
    Colorize(self, endStyled, notify.position)
end

function ColorSeg(self::Formatter, start, end_, styleName)
    end_ = end_ + 1
    stylenum = self.styles[styleName+1].stylenum
    while start < end_
        self.style_buffer[start+1] = stylenum
        start = start + 1
    end
end

function RegisterStyle(self::Formatter, style, stylenum = nothing)
    if stylenum === nothing
        stylenum = self.nextstylenum
        self.nextstylenum = self.nextstylenum + 1
    end
    RegisterStyle(FormatterBase, self, style)
end

function ColorizeString(self::Formatter, str, charStart, styleStart)
    throw(RuntimeError("You must override this method"))
end

function Colorize(self::Formatter, start = 0, end_ = -1)
    scintilla = self.scintilla
    stringVal = GetTextRange(scintilla, start, end_, decode = false)
    if start > 0
        stylenum = SCIGetStyleAt(scintilla, start - 1)
        styleStart = GetStyleByNum(self, stylenum).name
    else
        styleStart = nothing
    end
    SCIStartStyling(scintilla, start, 31)
    self.style_buffer = array(array, "b", repeat([(0,)...], length(stringVal)))
    ColorizeString(self, stringVal, styleStart)
    SCISetStylingEx(scintilla, self.style_buffer)
    self.style_buffer = nothing
    if self.bCompleteWhileIdle &&
       !(self.bHaveIdleHandler) &&
       end_ != -1 &&
       end_ < GetTextLength(scintilla)
        self.bHaveIdleHandler = 1
        AddIdleHandler(GetApp(win32ui), self.DoMoreColoring)
    end
end

function DoMoreColoring(self::Formatter, handler, count)::Bool
    try
        scintilla = self.scintilla
        endStyled = SCIGetEndStyled(scintilla)
        lineStartStyled = LineFromChar(scintilla, endStyled)
        start = LineIndex(scintilla, lineStartStyled)
        end_ = LineIndex(scintilla, lineStartStyled + 1)
        textlen = GetTextLength(scintilla)
        if end_ < 0
            end_ = textlen
        end
        finished = end_ >= textlen
        Colorize(self, start, end_)
    catch exn
        if exn isa (win32ui.error, AttributeError)
            finished = 1
        end
    end
    if finished
        self.bHaveIdleHandler = 0
        DeleteIdleHandler(GetApp(win32ui), handler)
    end
    return !(finished)
end

using keyword: iskeyword, kwlist
wordstarts = "_0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
wordchars = "._0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
operators = "%^&*()-+=|{}[]:;<>,/?!.~"
STYLE_DEFAULT = "Whitespace"
STYLE_COMMENT = "Comment"
STYLE_COMMENT_BLOCK = "Comment Blocks"
STYLE_NUMBER = "Number"
STYLE_STRING = "String"
STYLE_SQSTRING = "SQ String"
STYLE_TQSSTRING = "TQS String"
STYLE_TQDSTRING = "TQD String"
STYLE_KEYWORD = "Keyword"
STYLE_CLASS = "Class"
STYLE_METHOD = "Method"
STYLE_OPERATOR = "Operator"
STYLE_IDENTIFIER = "Identifier"
STYLE_BRACE = "Brace/Paren - matching"
STYLE_BRACEBAD = "Brace/Paren - unmatched"
STYLE_STRINGEOL = "String with no terminator"
STYLE_LINENUMBER = "Line numbers"
STYLE_INDENTGUIDE = "Indent guide"
STYLE_SELECTION = "Selection"
STRING_STYLES =
    [STYLE_STRING, STYLE_SQSTRING, STYLE_TQSSTRING, STYLE_TQDSTRING, STYLE_STRINGEOL]
PYTHON_STYLES = [
    (STYLE_DEFAULT, (0, 0, 200, 0, 8421504), CLR_INVALID, scintillacon.SCE_P_DEFAULT),
    (STYLE_COMMENT, (0, 2, 200, 0, 32768), CLR_INVALID, scintillacon.SCE_P_COMMENTLINE),
    (
        STYLE_COMMENT_BLOCK,
        (0, 2, 200, 0, 8421504),
        CLR_INVALID,
        scintillacon.SCE_P_COMMENTBLOCK,
    ),
    (STYLE_NUMBER, (0, 0, 200, 0, 8421376), CLR_INVALID, scintillacon.SCE_P_NUMBER),
    (STYLE_STRING, (0, 0, 200, 0, 32896), CLR_INVALID, scintillacon.SCE_P_STRING),
    (STYLE_SQSTRING, STYLE_STRING, CLR_INVALID, scintillacon.SCE_P_CHARACTER),
    (STYLE_TQSSTRING, STYLE_STRING, CLR_INVALID, scintillacon.SCE_P_TRIPLE),
    (STYLE_TQDSTRING, STYLE_STRING, CLR_INVALID, scintillacon.SCE_P_TRIPLEDOUBLE),
    (STYLE_STRINGEOL, (0, 0, 200, 0, 0), 32896, scintillacon.SCE_P_STRINGEOL),
    (STYLE_KEYWORD, (0, 1, 200, 0, 8388608), CLR_INVALID, scintillacon.SCE_P_WORD),
    (STYLE_CLASS, (0, 1, 200, 0, 16711680), CLR_INVALID, scintillacon.SCE_P_CLASSNAME),
    (STYLE_METHOD, (0, 1, 200, 0, 8421376), CLR_INVALID, scintillacon.SCE_P_DEFNAME),
    (STYLE_OPERATOR, (0, 0, 200, 0, 0), CLR_INVALID, scintillacon.SCE_P_OPERATOR),
    (STYLE_IDENTIFIER, (0, 0, 200, 0, 0), CLR_INVALID, scintillacon.SCE_P_IDENTIFIER),
]
SPECIAL_STYLES = [
    (STYLE_BRACE, (0, 0, 200, 0, 0), 16777088, scintillacon.STYLE_BRACELIGHT),
    (STYLE_BRACEBAD, (0, 0, 200, 0, 0), 9348594, scintillacon.STYLE_BRACEBAD),
    (
        STYLE_LINENUMBER,
        (0, 0, 200, 0, 0),
        GetSysColor(win32api, win32con.COLOR_3DFACE),
        scintillacon.STYLE_LINENUMBER,
    ),
    (STYLE_INDENTGUIDE, (0, 0, 200, 0, 0), CLR_INVALID, scintillacon.STYLE_INDENTGUIDE),
    (STYLE_SELECTION, (0, 0, 200, 0, CLR_INVALID), RGB(win32api, 192, 192, 192), 999999),
]
PythonSampleCode = "# Some Python\nclass Sample(Super):\n  def Fn(self):\n\tself.v = 1024\ndest = \'dest.html\'\nx = func(a + 1)|)\ns = \"I forget...\n## A large\n## comment block"
mutable struct PythonSourceFormatter <: AbstractPythonSourceFormatter
    string_style_names::Vector{String}

    PythonSourceFormatter(string_style_names::Vector{String} = STRING_STYLES) =
        new(string_style_names)
end
function GetSampleText(self::PythonSourceFormatter)::String
    return PythonSampleCode
end

function LoadStyles(self::PythonSourceFormatter)
    #= pass =#
end

function SetStyles(self::PythonSourceFormatter)
    for (name, format, bg, ignore) in PYTHON_STYLES
        RegisterStyle(self, Style(name, format, bg))
    end
    for (name, format, bg, sc_id) in SPECIAL_STYLES
        RegisterStyle(self, Style(name, format, bg), sc_id)
    end
end

function ClassifyWord(self::PythonSourceFormatter, cdoc, start, end_, prevWord)
    word = decode(cdoc[start+1:end_+1], "latin-1")
    attr = STYLE_IDENTIFIER
    if prevWord == "class"
        attr = STYLE_CLASS
    elseif prevWord == "def"
        attr = STYLE_METHOD
    elseif word[1] in string.digits
        attr = STYLE_NUMBER
    elseif iskeyword(word)
        attr = STYLE_KEYWORD
    end
    ColorSeg(self, start, end_, attr)
    return word
end

function ColorizeString(self::PythonSourceFormatter, str, styleStart)
    if styleStart === nothing
        styleStart = STYLE_DEFAULT
    end
    return ColorizePythonCode(self, str, 0, styleStart)
end

function ColorizePythonCode(self::PythonSourceFormatter, cdoc, charStart, styleStart)
    lengthDoc = length(cdoc)
    if lengthDoc <= charStart
        return
    end
    prevWord = ""
    state = styleStart
    chPrev = " "
    chPrev2 = " "
    chPrev3 = " "
    chNext2 = decode(cdoc[charStart+1:charStart+1], "latin-1")
    chNext = decode(cdoc[charStart+1:charStart+1], "latin-1")
    startSeg = charStart
    i = charStart
    while i < lengthDoc
        ch = chNext
        chNext = " "
        if (i + 1) < lengthDoc
            chNext = decode(cdoc[i+2:i+2], "latin-1")
        end
        chNext2 = " "
        if (i + 2) < lengthDoc
            chNext2 = decode(cdoc[i+3:i+3], "latin-1")
        end
        if state == STYLE_DEFAULT
            if ch in wordstarts
                ColorSeg(self, startSeg, i - 1, STYLE_DEFAULT)
                state = STYLE_KEYWORD
                startSeg = i
            elseif ch == "#"
                ColorSeg(self, startSeg, i - 1, STYLE_DEFAULT)
                if chNext == "#"
                    state = STYLE_COMMENT_BLOCK
                else
                    state = STYLE_COMMENT
                end
                startSeg = i
            elseif ch == "\""
                ColorSeg(self, startSeg, i - 1, STYLE_DEFAULT)
                startSeg = i
                state = STYLE_COMMENT
                if chNext == "\"" && chNext2 == "\""
                    i = i + 2
                    state = STYLE_TQDSTRING
                    ch = " "
                    chPrev = " "
                    chNext = " "
                    if (i + 1) < lengthDoc
                        chNext = cdoc[i+2]
                    end
                else
                    state = STYLE_STRING
                end
            elseif ch == "\'"
                ColorSeg(self, startSeg, i - 1, STYLE_DEFAULT)
                startSeg = i
                state = STYLE_COMMENT
                if chNext == "\'" && chNext2 == "\'"
                    i = i + 2
                    state = STYLE_TQSSTRING
                    ch = " "
                    chPrev = " "
                    chNext = " "
                    if (i + 1) < lengthDoc
                        chNext = cdoc[i+2]
                    end
                else
                    state = STYLE_SQSTRING
                end
            elseif ch in operators
                ColorSeg(self, startSeg, i - 1, STYLE_DEFAULT)
                ColorSeg(self, i, i, STYLE_OPERATOR)
                startSeg = i + 1
            end
        elseif state == STYLE_KEYWORD
            if ch ∉ wordchars
                prevWord = ClassifyWord(self, cdoc, startSeg, i - 1, prevWord)
                state = STYLE_DEFAULT
                startSeg = i
                if ch == "#"
                    if chNext == "#"
                        state = STYLE_COMMENT_BLOCK
                    else
                        state = STYLE_COMMENT
                    end
                elseif ch == "\""
                    if chNext == "\"" && chNext2 == "\""
                        i = i + 2
                        state = STYLE_TQDSTRING
                        ch = " "
                        chPrev = " "
                        chNext = " "
                        if (i + 1) < lengthDoc
                            chNext = cdoc[i+2]
                        end
                    else
                        state = STYLE_STRING
                    end
                elseif ch == "\'"
                    if chNext == "\'" && chNext2 == "\'"
                        i = i + 2
                        state = STYLE_TQSSTRING
                        ch = " "
                        chPrev = " "
                        chNext = " "
                        if (i + 1) < lengthDoc
                            chNext = cdoc[i+2]
                        end
                    else
                        state = STYLE_SQSTRING
                    end
                elseif ch in operators
                    ColorSeg(self, startSeg, i, STYLE_OPERATOR)
                    startSeg = i + 1
                end
            end
        elseif state == STYLE_COMMENT || state == STYLE_COMMENT_BLOCK
            if ch == "\r" || ch == "\n"
                ColorSeg(self, startSeg, i - 1, state)
                state = STYLE_DEFAULT
                startSeg = i
            end
        elseif state == STYLE_STRING
            if ch == "\\"
                if chNext == "\"" || chNext == "\'" || chNext == "\\"
                    i = i + 1
                    ch = chNext
                    chNext = " "
                    if (i + 1) < lengthDoc
                        chNext = cdoc[i+2]
                    end
                end
            elseif ch == "\""
                ColorSeg(self, startSeg, i, STYLE_STRING)
                state = STYLE_DEFAULT
                startSeg = i + 1
            end
        elseif state == STYLE_SQSTRING
            if ch == "\\"
                if chNext == "\"" || chNext == "\'" || chNext == "\\"
                    i = i + 1
                    ch = chNext
                    chNext = " "
                    if (i + 1) < lengthDoc
                        chNext = cdoc[i+2]
                    end
                end
            elseif ch == "\'"
                ColorSeg(self, startSeg, i, STYLE_SQSTRING)
                state = STYLE_DEFAULT
                startSeg = i + 1
            end
        elseif state == STYLE_TQSSTRING
            if ch == "\'" && chPrev == "\'" && chPrev2 == "\'" && chPrev3 != "\\"
                ColorSeg(self, startSeg, i, STYLE_TQSSTRING)
                state = STYLE_DEFAULT
                startSeg = i + 1
            end
        elseif state == STYLE_TQDSTRING &&
               ch == "\"" &&
               chPrev == "\"" &&
               chPrev2 == "\"" &&
               chPrev3 != "\\"
            ColorSeg(self, startSeg, i, STYLE_TQDSTRING)
            state = STYLE_DEFAULT
            startSeg = i + 1
        end
        chPrev3 = chPrev2
        chPrev2 = chPrev
        chPrev = ch
        i = i + 1
    end
    if startSeg < lengthDoc
        if state == STYLE_KEYWORD
            ClassifyWord(self, cdoc, startSeg, lengthDoc - 1, prevWord)
        else
            ColorSeg(self, startSeg, lengthDoc - 1, state)
        end
    end
end

source_formatter_extensions = [
    (split(".py .pys .pyw"), scintillacon.SCLEX_PYTHON),
    (split(".html .htm .asp .shtml"), scintillacon.SCLEX_HTML),
    (
        split("c .cc .cpp .cxx .h .hh .hpp .hxx .idl .odl .php3 .phtml .inc .js"),
        scintillacon.SCLEX_CPP,
    ),
    (split(".vbs .frm .ctl .cls"), scintillacon.SCLEX_VB),
    (split(".pl .pm .cgi .pod"), scintillacon.SCLEX_PERL),
    (split(".sql .spec .body .sps .spb .sf .sp"), scintillacon.SCLEX_SQL),
    (split(".tex .sty"), scintillacon.SCLEX_LATEX),
    (split(".xml .xul"), scintillacon.SCLEX_XML),
    (split(".err"), scintillacon.SCLEX_ERRORLIST),
    (split(".mak"), scintillacon.SCLEX_MAKEFILE),
    (split(".bat .cmd"), scintillacon.SCLEX_BATCH),
]
mutable struct BuiltinSourceFormatter <: AbstractBuiltinSourceFormatter
    ext
    nextstylenum

    BuiltinSourceFormatter(scintilla, ext) = begin
        FormatterBase(scintilla)
        new(scintilla, ext)
    end
end
function Colorize(self::BuiltinSourceFormatter, start = 0, end_ = -1)
    SendScintilla(self.scintilla, scintillacon.SCI_COLOURISE, start, end_)
end

function RegisterStyle(self::BuiltinSourceFormatter, style, stylenum = nothing)
    @assert(style.stylenum === nothing)
    if stylenum === nothing
        stylenum = self.nextstylenum
        self.nextstylenum = self.nextstylenum + 1
    end
    @assert(get(self.styles, stylenum) === nothing)
    style.stylenum = stylenum
    self.styles[style.name+1] = style
    self.styles_by_id[stylenum+1] = style
end

function HookFormatter(self::BuiltinSourceFormatter, parent = nothing)
    sc = self.scintilla
    for (exts, formatter) in source_formatter_extensions
        if self.ext in exts
            formatter_use = formatter
            break
        end
    end
    SendScintilla(sc, scintillacon.SCI_SETLEXER, formatter_use)
    keywords = join(kwlist, " ")
    SCISetKeywords(sc, keywords)
end

mutable struct BuiltinPythonSourceFormatter <: AbstractBuiltinPythonSourceFormatter
    ext::String
    sci_lexer_name
    string_style_names::Vector{String}

    BuiltinPythonSourceFormatter(
        sc,
        ext = ".py",
        sci_lexer_name = scintillacon.SCLEX_PYTHON,
        string_style_names::Vector{String} = STRING_STYLES,
    ) = begin
        BuiltinSourceFormatter(sc, ext)
        new(sc, ext, sci_lexer_name, string_style_names)
    end
end
function SetStyles(self::BuiltinPythonSourceFormatter)
    for (name, format, bg, sc_id) in PYTHON_STYLES
        RegisterStyle(self, Style(name, format, bg), sc_id)
    end
    for (name, format, bg, sc_id) in SPECIAL_STYLES
        RegisterStyle(self, Style(name, format, bg), sc_id)
    end
end

function GetSampleText(self::BuiltinPythonSourceFormatter)::String
    return PythonSampleCode
end

end
