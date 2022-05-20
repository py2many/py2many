using OrderedCollections
using PyCall
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")
DBGSTATE_NOT_DEBUGGING = 0
DBGSTATE_RUNNING = 1
DBGSTATE_BREAK = 2
DBGSTATE_QUITTING = 3
LINESTATE_CURRENT = 1
LINESTATE_BREAKPOINT = 2
LINESTATE_CALLSTACK = 4
OPT_HIDE = "hide"
OPT_STOP_EXCEPTIONS = "stopatexceptions"

function DoGetOption(optsDict, optName, default)
    optsDict[optName+1] = GetProfileVal(win32ui, "Debugger Options", optName, default)
end

function LoadDebuggerOptions()::Dict
    opts = OrderedDict()
    DoGetOption(opts, OPT_HIDE, 0)
    DoGetOption(opts, OPT_STOP_EXCEPTIONS, 1)
    return opts
end

function SaveDebuggerOptions(opts)
    for (key, val) in items(opts)
        WriteProfileVal(win32ui, "Debugger Options", key, val)
    end
end
