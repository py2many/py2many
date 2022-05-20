using PyCall
using StringEncodings
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
using win32com_.gen_py.docking.DockingBar: DockingBar

import code
import string

import win32clipboard
import win32con

import afxres

import __main__
import win32com_.gen_py.scintilla.formatter
import win32com_.gen_py.scintilla.control
import win32com_.gen_py.scintilla.IDLEenvironment
import win32com_.gen_py.framework.app
ID_EDIT_COPY_CODE = 925698
ID_EDIT_EXEC_CLIPBOARD = 8195
trace = win32com_.gen_py.scintilla.formatter.trace
abstract type AbstractInteractiveFormatter <: AbstractFormatterParent end
abstract type AbstractPythonwinInteractiveInterpreter <: Abstractcode.InteractiveInterpreter end
abstract type AbstractInteractiveCore end
abstract type AbstractInteractiveView <: AbstractInteractiveCore end
abstract type AbstractCInteractivePython <: Abstractwinout.WindowOutput end
abstract type AbstractInteractiveFrame <: Abstractwinout.WindowOutputFrame end
abstract type AbstractDockedInteractiveView <: AbstractDockedInteractiveViewParent end
abstract type AbstractCDockedInteractivePython <: AbstractCInteractivePython end
include("winout.jl")

_is_block_opener = compile(re, ":\\s*(#.*)?\$").search
_is_block_closer =
    compile(
        re,
        "\n    \\s*\n    ( return\n    | break\n    | continue\n    | raise\n    | pass\n    )\n    \\b\n",
        re.VERBOSE,
    ).match
tracebackHeader = encode("Traceback (", "ascii")
sectionProfile = "Interactive Window"
valueFormatTitle = "FormatTitle"
valueFormatInput = "FormatInput"
valueFormatOutput = "FormatOutput"
valueFormatOutputError = "FormatOutputError"
formatTitle = (-536870897, 0, 220, 0, 16711680, 184, 34, "Arial")
formatInput = (-402653169, 0, 200, 0, 0, 0, 49, "Courier New")
formatOutput = (-402653169, 0, 200, 0, 8421376, 0, 49, "Courier New")
formatOutputError = (-402653169, 0, 200, 0, 255, 0, 49, "Courier New")
try
    sys.ps1
catch exn
    if exn isa AttributeError
        sys.ps1 = ">>> "
        sys.ps2 = "... "
    end
end
function LoadPreference(preference, default = "")
    return GetProfileVal(win32ui, sectionProfile, preference, default)
end

function SavePreference(prefName, prefValue)
    WriteProfileVal(win32ui, sectionProfile, prefName, prefValue)
end

function GetPromptPrefix(line)
    ps1 = sys.ps1
    if line[begin:length(ps1)] == ps1
        return ps1
    end
    ps2 = sys.ps2
    if line[begin:length(ps2)] == ps2
        return ps2
    end
end

STYLE_INTERACTIVE_EOL = "Interactive EOL"
STYLE_INTERACTIVE_OUTPUT = "Interactive Output"
STYLE_INTERACTIVE_PROMPT = "Interactive Prompt"
STYLE_INTERACTIVE_BANNER = "Interactive Banner"
STYLE_INTERACTIVE_ERROR = "Interactive Error"
STYLE_INTERACTIVE_ERROR_FINALLINE = "Interactive Error (final line)"
INTERACTIVE_STYLES = [
    STYLE_INTERACTIVE_EOL,
    STYLE_INTERACTIVE_OUTPUT,
    STYLE_INTERACTIVE_PROMPT,
    STYLE_INTERACTIVE_BANNER,
    STYLE_INTERACTIVE_ERROR,
    STYLE_INTERACTIVE_ERROR_FINALLINE,
]
FormatterParent = win32com_.gen_py.scintilla.formatter.PythonSourceFormatter
mutable struct InteractiveFormatter <: AbstractInteractiveFormatter
    bannerDisplayed::Bool
    style_buffer

    InteractiveFormatter(scintilla) = begin
        FormatterParent.__init__(self, scintilla)
        new(scintilla)
    end
end
function SetStyles(self::InteractiveFormatter)
    SetStyles(FormatterParent)
    Style = win32com_.gen_py.scintilla.formatter.Style
    RegisterStyle(self, Style(STYLE_INTERACTIVE_EOL, STYLE_INTERACTIVE_PROMPT))
    RegisterStyle(self, Style(STYLE_INTERACTIVE_PROMPT, formatInput))
    RegisterStyle(self, Style(STYLE_INTERACTIVE_OUTPUT, formatOutput))
    RegisterStyle(self, Style(STYLE_INTERACTIVE_BANNER, formatTitle))
    RegisterStyle(self, Style(STYLE_INTERACTIVE_ERROR, formatOutputError))
    RegisterStyle(self, Style(STYLE_INTERACTIVE_ERROR_FINALLINE, STYLE_INTERACTIVE_ERROR))
end

function LoadPreference(self::InteractiveFormatter, name, default)
    rc = GetProfileVal(win32ui, "Format", name, default)
    if rc == default
        rc = GetProfileVal(win32ui, sectionProfile, name, default)
    end
    return rc
end

function ColorizeInteractiveCode(self::InteractiveFormatter, cdoc, styleStart, stylePyStart)
    lengthDoc = length(cdoc)
    if lengthDoc == 0
        return
    end
    state = styleStart
    chNext = decode(cdoc[1:1], "latin-1")
    startSeg = 0
    i = 0
    lastState = state
    while i < lengthDoc
        ch = chNext
        chNext = decode(cdoc[i+2:i+2], "latin-1")
        if state == STYLE_INTERACTIVE_EOL
            if ch ∉ "\r\n"
                ColorSeg(self, startSeg, i - 1, state)
                startSeg = i
                if ch ∈ [sys.ps1[1], sys.ps2[1]]
                    state = STYLE_INTERACTIVE_PROMPT
                elseif cdoc[i+1:i+length(tracebackHeader)] == tracebackHeader
                    state = STYLE_INTERACTIVE_ERROR
                else
                    state = STYLE_INTERACTIVE_OUTPUT
                end
            end
        elseif state == STYLE_INTERACTIVE_PROMPT
            if ch ∉ ((sys.ps1 + sys.ps2) + " ")
                ColorSeg(self, startSeg, i - 1, state)
                startSeg = i
                if ch ∈ "\r\n"
                    state = STYLE_INTERACTIVE_EOL
                else
                    state = stylePyStart
                end
            end
        elseif state ∈ [STYLE_INTERACTIVE_OUTPUT]
            if ch ∈ "\r\n"
                ColorSeg(self, startSeg, i - 1, state)
                startSeg = i
                state = STYLE_INTERACTIVE_EOL
            end
        elseif state == STYLE_INTERACTIVE_ERROR
            if ch ∈ "\r\n" && chNext && chNext ∉ string.whitespace
                ColorSeg(self, startSeg, i, state)
                startSeg = i + 1
                state = STYLE_INTERACTIVE_ERROR_FINALLINE
            elseif i == 0 && ch ∉ string.whitespace
                ColorSeg(self, startSeg, i - 1, state)
                startSeg = i
                state = STYLE_INTERACTIVE_ERROR_FINALLINE
            end
        elseif state == STYLE_INTERACTIVE_ERROR_FINALLINE
            if ch ∈ "\r\n"
                ColorSeg(self, startSeg, i - 1, state)
                startSeg = i
                state = STYLE_INTERACTIVE_EOL
            end
        elseif state == STYLE_INTERACTIVE_BANNER
            if ch ∈ "\r\n" && chNext == "" || chNext ∈ ">["
                ColorSeg(self, startSeg, i - 1, state)
                startSeg = i
                state = STYLE_INTERACTIVE_EOL
            end
        else
            end_ = startSeg
            while end_ < lengthDoc && cdoc[end_] ∉ encode("\r\n", "ascii")
                end_ = end_ + 1
            end
            ColorizePythonCode(self, cdoc[begin:end_], startSeg, state)
            stylePyStart = GetStringStyle(self, end_ - 1)
            if stylePyStart === nothing
                stylePyStart = win32com_.gen_py.scintilla.formatter.STYLE_DEFAULT
            else
                stylePyStart = stylePyStart.name
            end
            startSeg = end_
            i = end_ - 1
            chNext = decode(cdoc[end_+1:end_+1], "latin-1")
            state = STYLE_INTERACTIVE_EOL
        end
        if lastState != state
            lastState = state
        end
        i = i + 1
    end
    if startSeg < i
        ColorSeg(self, startSeg, i - 1, state)
    end
end

function Colorize(self::InteractiveFormatter, start = 0, end_ = -1)
    stringVal = GetTextRange(self.scintilla, start, end_, false)
    styleStart = nothing
    stylePyStart = nothing
    if start > 1
        look = start - 1
        while look && SCIGetCharAt(self.scintilla, look) ∈ "\n\r"
            look = look - 1
        end
        if look && look < (start - 1)
            strstyle = GetStringStyle(self, look)
            quote_char = nothing
            if strstyle != nothing
                if strstyle.name == win32com_.gen_py.scintilla.formatter.STYLE_TQSSTRING
                    quote_char = "\'"
                elseif strstyle.name == win32com_.gen_py.scintilla.formatter.STYLE_TQDSTRING
                    quote_char = "\""
                end
                if quote_char != nothing
                    if look > 2
                        look_str =
                            (
                                SCIGetCharAt(self.scintilla, look - 2) +
                                SCIGetCharAt(self.scintilla, look - 1)
                            ) + SCIGetCharAt(self.scintilla, look)
                        if look_str != (quote_char * 3)
                            stylePyStart = strstyle.name
                        end
                    end
                end
            end
        end
    end
    if stylePyStart === nothing
        stylePyStart = win32com_.gen_py.scintilla.formatter.STYLE_DEFAULT
    end
    if start > 0
        stylenum = SCIGetStyleAt(self.scintilla, start - 1)
        styleStart = GetStyleByNum(self, stylenum).name
    elseif self.bannerDisplayed
        styleStart = STYLE_INTERACTIVE_EOL
    else
        styleStart = STYLE_INTERACTIVE_BANNER
        self.bannerDisplayed = true
    end
    SCIStartStyling(self.scintilla, start, 31)
    self.style_buffer = array(array, "b", repeat([(0,)...], length(stringVal)))
    ColorizeInteractiveCode(self, stringVal, styleStart, stylePyStart)
    SCISetStylingEx(self.scintilla, self.style_buffer)
    self.style_buffer = nothing
end

mutable struct PythonwinInteractiveInterpreter <: AbstractPythonwinInteractiveInterpreter
    globals
    locals

    PythonwinInteractiveInterpreter(locals = nothing, globals = nothing) = begin
        if locals === nothing
            locals = __main__.__dict__
        end
        if globals === nothing
            globals = locals
        end
        code.InteractiveInterpreter.__init__(self, locals)
        new(locals, globals)
    end
end
function showsyntaxerror(self::PythonwinInteractiveInterpreter, filename = nothing)
    write(sys.stderr, decode(tracebackHeader, "ascii"))
    showsyntaxerror(code.InteractiveInterpreter, self)
end

function runcode(self::PythonwinInteractiveInterpreter, code)
    try
        exec(code, self.globals, self.locals)
    catch exn
        if exn isa SystemExit
            error()
        end
        showtraceback(self)
    end
end

mutable struct InteractiveCore <: AbstractInteractiveCore
    banner
    oldStdOut
    oldStdErr
    interp::AbstractPythonwinInteractiveInterpreter
    history
    OnSelectBlock
    OnEditCopyCode
    OnEditExecClipboard
end
function Init(self::InteractiveCore)
    self.oldStdOut = nothing
    self.oldStdErr = nothing
    self.interp = PythonwinInteractiveInterpreter()
    OutputGrab(self)
    if GetTextLength(self) == 0
        if self.banner === nothing
            suffix = ""
            if win32ui.debug
                suffix = ", debug build"
            end
            write(
                sys.stderr,
                "PythonWin %s on %s%s.\n" % (sys.version, sys.platform, suffix),
            )
            write(
                sys.stderr,
                "Portions %s - see \'Help/About PythonWin\' for further copyright information.\n" %
                (win32ui.copyright,),
            )
        else
            write(sys.stderr, banner)
        end
    end
    rcfile = get(os.environ, "PYTHONSTARTUP")
    if rcfile
        try
            exec(
                compile(read(readline(rcfile)), rcfile, "exec", true),
                __main__.__dict__,
                __main__.__dict__,
            )
        catch exn
            write(sys.stderr, ">>> \nError executing PYTHONSTARTUP script %r\n" % rcfile)
            current_exceptions() != [] ? current_exceptions()[end] : nothing
        end
    end
    AppendToPrompt(self, [])
end

function SetContext(self::InteractiveCore, globals, locals, name = "Dbg")
    oldPrompt = sys.ps1
    if globals === nothing
        sys.ps1 = ">>> "
        sys.ps2 = "... "
        locals = __main__.__dict__
        globals = __main__.__dict__
    else
        sys.ps1 = "[%s]>>> " % name
        sys.ps2 = "[%s]... " % name
    end
    self.interp.locals = locals
    self.interp.globals = globals
    AppendToPrompt(self, [], oldPrompt)
end

function GetContext(self::InteractiveCore)::Tuple
    return (self.interp.globals, self.interp.locals)
end

function DoGetLine(self::InteractiveCore, line = -1)
    if line == -1
        line = LineFromChar(self)
    end
    line = GetLine(self, line)
    while line && line[end] ∈ ["\r", "\n"]
        line = line[begin:-1]
    end
    return line
end

function AppendToPrompt(self::InteractiveCore, bufLines, oldPrompt = nothing)
    #= Take a command and stick it at the end of the buffer (with python prompts inserted if required). =#
    flush(self)
    lastLineNo = GetLineCount(self) - 1
    line = DoGetLine(self, lastLineNo)
    if oldPrompt && line == oldPrompt
        SetSel(self, GetTextLength(self) - length(oldPrompt), GetTextLength(self))
        ReplaceSel(self, sys.ps1)
    elseif line != string(sys.ps1)
        if length(line) != 0
            write(self, "\n")
        end
        write(self, sys.ps1)
    end
    flush(self)
    mark_set(self.idle.text, "iomark", "end-1c")
    if !(bufLines)
        return
    end
    terms = append!(repeat(["\n" + sys.ps2], (length(bufLines) - 1)), [""])
    for (bufLine, term) in zip(bufLines, terms)
        if strip(bufLine)
            write(self, bufLine + term)
        end
    end
    flush(self)
end

function EnsureNoPrompt(self::InteractiveCore)
    flush(self)
    lastLineNo = GetLineCount(self) - 1
    line = DoGetLine(self, lastLineNo)
    if !(line) || line ∈ [sys.ps1, sys.ps2]
        SetSel(self, GetTextLength(self) - length(line), GetTextLength(self))
        ReplaceSel(self, "")
    else
        write(self, "\n")
    end
end

function _GetSubConfigNames(self::InteractiveCore)
    return ["interactive"]
end

function HookHandlers(self::InteractiveCore)
    HookCommand(self, self.OnSelectBlock, win32ui.ID_EDIT_SELECT_BLOCK)
    HookCommand(self, self.OnEditCopyCode, ID_EDIT_COPY_CODE)
    HookCommand(self, self.OnEditExecClipboard, ID_EDIT_EXEC_CLIPBOARD)
    mod = GetIDLEModule(win32com_.gen_py.scintilla.IDLEenvironment, "IdleHistory")
    if mod != nothing
        self.history = History(mod, self.idle.text, "\n" + sys.ps2)
    else
        self.history = nothing
    end
end

function GetBlockBoundary(self::InteractiveCore, lineNo)::Tuple
    line = DoGetLine(self, lineNo)
    maxLineNo = GetLineCount(self) - 1
    prefix = GetPromptPrefix(line)
    if prefix === nothing
        flag = 0
        startLineNo = lineNo
        while startLineNo > 0
            if GetPromptPrefix(DoGetLine(self, startLineNo - 1)) != nothing
                has_break = true
                break
            end
            startLineNo = startLineNo - 1
        end
        endLineNo = lineNo
        while endLineNo < maxLineNo
            if GetPromptPrefix(DoGetLine(self, endLineNo + 1)) != nothing
                has_break = true
                break
            end
            endLineNo = endLineNo + 1
        end
    else
        flag = 1
        startLineNo = lineNo
        while startLineNo > 0 && prefix != string(sys.ps1)
            prefix = GetPromptPrefix(DoGetLine(self, startLineNo - 1))
            if prefix === nothing
                has_break = true
                break
            end
            startLineNo = startLineNo - 1
        end
        endLineNo = lineNo
        while endLineNo < maxLineNo
            prefix = GetPromptPrefix(DoGetLine(self, endLineNo + 1))
            if prefix === nothing
                has_break = true
                break
            end
            if prefix == string(sys.ps1)
                has_break = true
                break
            end
            endLineNo = endLineNo + 1
        end
    end
    return (startLineNo, endLineNo, flag)
end

function ExtractCommand(self::InteractiveCore, lines)::Vector
    start, end_ = lines
    retList = []
    while end_ >= start
        thisLine = DoGetLine(self, end_)
        promptLen = length(GetPromptPrefix(thisLine))
        retList = append!([thisLine[promptLen+1:end]], retList)
        end_ = end_ - 1
    end
    return retList
end

function OutputGrab(self::InteractiveCore)
    self.oldStdOut = sys.stdout
    self.oldStdErr = sys.stderr
    sys.stdout = self
    sys.stderr = self
    flush(self)
end

function OutputRelease(self::InteractiveCore)
    if self.oldStdOut != nothing
        if sys.stdout === self
            sys.stdout = self.oldStdOut
        end
    end
    if self.oldStdErr != nothing
        if sys.stderr === self
            sys.stderr = self.oldStdErr
        end
    end
    self.oldStdOut = nothing
    self.oldStdErr = nothing
    flush(self)
end

function ProcessEnterEvent(self::InteractiveCore, event)::Int64
    if SCIAutoCActive(self)
        SCIAutoCComplete(self)
        SCICancel(self)
        return
    end
    SCICancel(self)
    haveGrabbedOutput = 0
    if HandleSpecialLine(self)
        return 0
    end
    lineNo = LineFromChar(self)
    start, end_, isCode = GetBlockBoundary(self, lineNo)
    if !(isCode)
        AppendToPrompt(self, [])
        SetStatusText(win32ui, LoadString(win32ui, afxres.AFX_IDS_IDLEMESSAGE))
        return
    end
    lines = ExtractCommand(self, (start, end_))
    if end_ != (GetLineCount(self) - 1)
        SetStatusText(win32ui, "Press ENTER to execute command")
        AppendToPrompt(self, lines)
        SetSel(self, -2)
        return
    end
    bNeedIndent =
        GetKeyState(win32api, win32con.VK_SHIFT) < 0 ||
        GetKeyState(win32api, win32con.VK_CONTROL) < 0
    if bNeedIndent
        ReplaceSel(self, "\n")
    else
        SetSel(self, -2)
        ReplaceSel(self, "\n")
        source = join(lines, "\n")
        while source && source[end] ∈ "\t "
            source = source[begin:-1]
        end
        OutputGrab(self)
        try
            if runsource(self.interp, source, "<interactive input>")
                bNeedIndent = 1
            else
                if self.history != nothing
                    history_store(self.history, source)
                end
                AppendToPrompt(self, [])
                SetStatusText(win32ui, LoadString(win32ui, afxres.AFX_IDS_IDLEMESSAGE))
            end
        finally
            OutputRelease(self)
        end
    end
    if bNeedIndent
        SetStatusText(win32ui, "Ready to continue the command")
        curLine = DoGetLine(self, lineNo)[length(sys.ps2)+1:end]
        pos = 0
        indent = ""
        while length(curLine) > pos && curLine[pos+1] ∈ string.whitespace
            indent = indent + curLine[pos+1]
            pos = pos + 1
        end
        if _is_block_opener(curLine)
            indent = indent * "\t"
        elseif _is_block_closer(curLine)
            indent = indent[begin:-1]
        end
        ReplaceSel(self, sys.ps2 + indent)
    end
    return 0
end

function ProcessEscEvent(self::InteractiveCore, event)::Int64
    if SCIAutoCActive(self) || SCICallTipActive(self)
        SCICancel(self)
    else
        SetStatusText(win32ui, "Cancelled.")
        AppendToPrompt(self, ("",))
    end
    return 0
end

function OnSelectBlock(self::InteractiveCore, command, code)
    lineNo = LineFromChar(self)
    start, end_, isCode = GetBlockBoundary(self, lineNo)
    startIndex = LineIndex(self, start)
    endIndex = LineIndex(self, end_ + 1) - 2
    if endIndex < 0
        endIndex = -2
    end
    SetSel(self, startIndex, endIndex)
end

function OnEditCopyCode(self::InteractiveCore, command, code)
    #= Sanitizes code from interactive window, removing prompts and output,
            and inserts it in the clipboard. =#
    code = GetSelText(self)
    lines = splitlines(code)
    out_lines = []
    for line in lines
        if startswith(line, sys.ps1)
            line = line[length(sys.ps1)+1:end]
            push!(out_lines, line)
        elseif startswith(line, sys.ps2)
            line = line[length(sys.ps2)+1:end]
            push!(out_lines, line)
        end
    end
    out_code = join(out_lines, os.linesep)
    OpenClipboard(win32clipboard)
    try
        SetClipboardData(win32clipboard, win32clipboard.CF_UNICODETEXT, string(out_code))
    finally
        CloseClipboard(win32clipboard)
    end
end

function OnEditExecClipboard(self::InteractiveCore, command, code)
    #= Executes python code directly from the clipboard. =#
    OpenClipboard(win32clipboard)
    try
        code = GetClipboardData(win32clipboard, win32clipboard.CF_UNICODETEXT)
    finally
        CloseClipboard(win32clipboard)
    end
    code = replace(code, "\r\n", "\n") + "\n"
    try
        o = compile(code, "<clipboard>", "exec")
        exec(o, __main__.__dict__)
    catch exn
        current_exceptions() != [] ? current_exceptions()[end] : nothing
    end
end

function GetRightMenuItems(self::InteractiveCore)::Vector
    ret = []
    flags = 0
    push!(ret, (flags, win32ui.ID_EDIT_UNDO, "&Undo"))
    push!(ret, win32con.MF_SEPARATOR)
    push!(ret, (flags, win32ui.ID_EDIT_CUT, "Cu&t"))
    push!(ret, (flags, win32ui.ID_EDIT_COPY, "&Copy"))
    start, end_ = GetSel(self)
    if start != end_
        push!(ret, (flags, ID_EDIT_COPY_CODE, "Copy code without prompts"))
    end
    if IsClipboardFormatAvailable(win32clipboard, win32clipboard.CF_UNICODETEXT)
        push!(ret, (flags, ID_EDIT_EXEC_CLIPBOARD, "Execute python code from clipboard"))
    end
    push!(ret, (flags, win32ui.ID_EDIT_PASTE, "&Paste"))
    push!(ret, win32con.MF_SEPARATOR)
    push!(ret, (flags, win32ui.ID_EDIT_SELECT_ALL, "&Select all"))
    push!(ret, (flags, win32ui.ID_EDIT_SELECT_BLOCK, "Select &block"))
    push!(ret, (flags, win32ui.ID_VIEW_WHITESPACE, "View &Whitespace"))
    return ret
end

function MDINextEvent(self::InteractiveCore, event)
    MDINext(GetMainFrame(win32ui), 0)
end

function MDIPrevEvent(self::InteractiveCore, event)
    MDINext(GetMainFrame(win32ui), 0)
end

function WindowBackEvent(self::InteractiveCore, event)
    parent = GetParentFrame(self)
    if parent == GetMainFrame(win32ui)
        try
            wnd, isactive = MDIGetActive(parent)
            SetFocus(wnd)
        catch exn
            if exn isa win32ui.error
                #= pass =#
            end
        end
    else
        try
            lastActive = GetParentFrame(self).lastActive
            if lastActive != nothing && lastActive._obj_ === nothing ||
               GetSafeHwnd(lastActive) == 0
                lastActive = nothing
                GetParentFrame(self).lastActive = nothing
                SetStatusText(win32ui, "The last active Window has been closed.")
            end
        catch exn
            if exn isa AttributeError
                println("Can\'t find the last active window!")
                lastActive = nothing
            end
        end
        if lastActive != nothing
            MDIActivate(lastActive)
        end
    end
end

mutable struct InteractiveView <: AbstractInteractiveView
    encoding

    InteractiveView(doc) = begin
        InteractiveCore()
        winout.WindowOutputView.__init__(self, doc)
        new(doc)
    end
end
function _MakeColorizer(self::InteractiveView)::InteractiveFormatter
    return InteractiveFormatter(self)
end

function OnInitialUpdate(self::InteractiveView)
    OnInitialUpdate(winout.WindowOutputView)
    SetWordWrap(self)
    Init(self)
end

function HookHandlers(self::InteractiveView)
    HookHandlers(winout.WindowOutputView)
    HookHandlers(InteractiveCore)
end

mutable struct CInteractivePython <: AbstractCInteractivePython
    IsFinalDestroy::Int64
    makeDoc
    makeFrame

    CInteractivePython(makeDoc = nothing, makeFrame = nothing) = begin
        winout.WindowOutput.__init__(
            self,
            sectionProfile,
            sectionProfile,
            winout.flags.WQ_LINE,
            1,
            nothing,
            makeDoc,
            makeFrame,
            InteractiveView,
        )
        Create()
        new(makeDoc, makeFrame)
    end
end
function OnViewDestroy(self::CInteractivePython, view)
    if self.IsFinalDestroy != 0
        OutputRelease(view)
    end
    OnViewDestroy(winout.WindowOutput, self)
end

function Close(self::CInteractivePython)
    self.IsFinalDestroy = 1
    Close(winout.WindowOutput)
end

mutable struct InteractiveFrame <: AbstractInteractiveFrame
    lastActive

    InteractiveFrame() = begin
        winout.WindowOutputFrame.__init__(self)
        new()
    end
end
function OnMDIActivate(self::InteractiveFrame, bActive, wndActive, wndDeactive)
    if bActive
        self.lastActive = wndDeactive
    end
end

ID_DOCKED_INTERACTIVE_CONTROLBAR = 59394
DockedInteractiveViewParent = InteractiveView
mutable struct DockedInteractiveView <: AbstractDockedInteractiveView
    OnSetFocus
    OnKillFocus
end
function HookHandlers(self::DockedInteractiveView)
    HookHandlers(DockedInteractiveViewParent)
    HookMessage(self, self.OnSetFocus, win32con.WM_SETFOCUS)
    HookMessage(self, self.OnKillFocus, win32con.WM_KILLFOCUS)
end

function OnSetFocus(self::DockedInteractiveView, msg)::Int64
    SetActiveView(GetParentFrame(self), self)
    return 1
end

function OnKillFocus(self::DockedInteractiveView, msg)::Int64
    hwnd = msg[3]
    wparam = msg[3]
    try
        wnd = CreateWindowFromHandle(win32ui, hwnd)
        reset = GetTopLevelFrame(wnd) == GetTopLevelFrame(self)
    catch exn
        if exn isa win32ui.error
            reset = 0
        end
    end
    if reset
        SetActiveView(GetParentFrame(self), nothing)
    end
    return 1
end

function OnDestroy(self::DockedInteractiveView, msg)
    newSize = GetWindowPlacement(self)[5]
    SaveWindowSize(win32com_.gen_py.framework.app, "Interactive Window", newSize, "docked")
    try
        if GetParentFrame(self).GetActiveView == self
            SetActiveView(GetParentFrame(self), nothing)
        end
    catch exn
        if exn isa win32ui.error
            #= pass =#
        end
    end
    try
        if GetActiveView(GetMainFrame(win32ui)) == self
            SetActiveView(GetMainFrame(win32ui), nothing)
        end
    catch exn
        if exn isa win32ui.error
            #= pass =#
        end
    end
    return OnDestroy(DockedInteractiveViewParent, self)
end

mutable struct CDockedInteractivePython <: AbstractCDockedInteractivePython
    bFirstCreated::Int64
    dockbar
    bCreating::Int64
    currentView
    title

    CDockedInteractivePython(dockbar) = begin
        CInteractivePython()
        new(dockbar)
    end
end
function NeedRecreateWindow(self::CDockedInteractivePython)::Int64
    if self.bCreating
        return 0
    end
    try
        frame = GetMainFrame(win32ui)
        if frame.closing
            return 0
        end
    catch exn
        if exn isa (win32ui.error, AttributeError)
            return 0
        end
    end
    try
        cb = GetControlBar(frame, ID_DOCKED_INTERACTIVE_CONTROLBAR)
        return !IsWindowVisible(cb)
    catch exn
        if exn isa win32ui.error
            return 1
        end
    end
end

function RecreateWindow(self::CDockedInteractivePython)
    try
        dockbar = GetControlBar(GetMainFrame(win32ui), ID_DOCKED_INTERACTIVE_CONTROLBAR)
        ShowControlBar(GetMainFrame(win32ui), dockbar, 1, 1)
    catch exn
        if exn isa win32ui.error
            CreateDockedInteractiveWindow()
        end
    end
end

function Create(self::CDockedInteractivePython)
    self.bCreating = 1
    doc = InteractiveDocument(nothing, DoCreateDoc(self))
    view = DockedInteractiveView(doc)
    defRect = LoadWindowSize(win32com_.gen_py.framework.app, "Interactive Window", "docked")
    if (defRect[3] - defRect[1]) == 0
        defRect = (0, 0, 500, 200)
    end
    style = (win32con.WS_CHILD | win32con.WS_VISIBLE) | win32con.WS_BORDER
    id = 1050
    CreateWindow(view, self.dockbar, id, style, defRect)
    OnInitialUpdate(view)
    self.bFirstCreated = 1
    self.currentView = GetFirstView(doc)
    self.bCreating = 0
    if self.title
        SetTitle(doc, self.title)
    end
end

function InteractiveViewCreator(parent)
    global edit
    edit = CDockedInteractivePython(parent)
    return edit.currentView
end

function CreateDockedInteractiveWindow()
    bar = DockingBar()
    creator = InteractiveViewCreator
    CreateWindow(
        bar,
        GetMainFrame(win32ui),
        creator,
        "Interactive Window",
        ID_DOCKED_INTERACTIVE_CONTROLBAR,
    )
    SetBarStyle(
        bar,
        ((GetBarStyle(bar) | afxres.CBRS_TOOLTIPS) | afxres.CBRS_FLYBY) |
        afxres.CBRS_SIZE_DYNAMIC,
    )
    EnableDocking(bar, afxres.CBRS_ALIGN_ANY)
    DockControlBar(GetMainFrame(win32ui), bar, afxres.AFX_IDW_DOCKBAR_BOTTOM)
end

InteractiveDocument = winout.WindowOutputDocument
edit = nothing
function CreateInteractiveWindowUserPreference(makeDoc = nothing, makeFrame = nothing)
    #= Create some sort of interactive window if the user's preference say we should. =#
    bCreate = LoadPreference("Show at startup", 1)
    if bCreate
        CreateInteractiveWindow(makeDoc, makeFrame)
    end
end

function CreateInteractiveWindow(makeDoc = nothing, makeFrame = nothing)
    #= Create a standard or docked interactive window unconditionally =#
    @assert(edit === nothing)
    bDocking = LoadPreference("Docking", 0)
    if bDocking
        CreateDockedInteractiveWindow()
    else
        CreateMDIInteractiveWindow(makeDoc, makeFrame)
    end
    @assert(edit != nothing)
    SetFocus(edit.currentView)
end

function CreateMDIInteractiveWindow(makeDoc = nothing, makeFrame = nothing)
    #= Create a standard (non-docked) interactive window unconditionally =#
    global edit
    if makeDoc === nothing
        makeDoc = InteractiveDocument
    end
    if makeFrame === nothing
        makeFrame = InteractiveFrame
    end
    edit = CInteractivePython(makeDoc, makeFrame)
end

function DestroyInteractiveWindow()
    #= Destroy the interactive window.
        This is different to Closing the window,
        which may automatically re-appear.  Once destroyed, it can never be recreated,
        and a complete new instance must be created (which the various other helper
        functions will then do after making this call
         =#
    global edit
    if edit != nothing && edit.currentView != nothing
        if GetParentFrame(edit.currentView) == GetMainFrame(win32ui)
            #= pass =#
        else
            Close(edit)
            edit = nothing
        end
    end
end

function CloseInteractiveWindow()
    #= Close the interactive window, allowing it to be re-created on demand. =#
    global edit
    if edit != nothing && edit.currentView != nothing
        if GetParentFrame(edit.currentView) == GetMainFrame(win32ui)
            frame = GetMainFrame(win32ui)
            cb = GetControlBar(frame, ID_DOCKED_INTERACTIVE_CONTROLBAR)
            ShowControlBar(frame, cb, 0, 1)
        else
            DestroyWindow(GetParentFrame(edit.currentView))
        end
    end
end

function ToggleInteractiveWindow()
    #= If the interactive window is visible, hide it, otherwise show it. =#
    if edit === nothing
        CreateInteractiveWindow()
    elseif NeedRecreateWindow(edit)
        RecreateWindow(edit)
    else
        CloseInteractiveWindow()
    end
end

function ShowInteractiveWindow()
    #= Shows (or creates if necessary) an interactive window =#
    if edit === nothing
        CreateInteractiveWindow()
    elseif NeedRecreateWindow(edit)
        RecreateWindow(edit)
    else
        parent = GetParentFrame(edit.currentView)
        if parent == GetMainFrame(win32ui)
            SetFocus(edit.currentView)
        else
            AutoRestore(GetParentFrame(edit.currentView))
            MDIActivate(GetMainFrame(win32ui), GetParentFrame(edit.currentView))
        end
    end
end

function IsInteractiveWindowVisible()
    return edit != nothing && !NeedRecreateWindow(edit)
end
