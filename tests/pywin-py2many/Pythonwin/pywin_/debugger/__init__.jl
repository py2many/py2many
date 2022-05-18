using PyCall
win32ui = pyimport("win32ui")

import win32com_.gen_py.framework.app
include("dbgpyapp.jl")
include("debugger.jl")

function _MakeDebuggerGUI()
    InitInstance(app)
end

isInprocApp = -1
function _CheckNeedGUI()
    global isInprocApp
    if isInprocApp == -1
        isInprocApp = IsInproc(GetApp(win32ui))
    end
    if isInprocApp != 0
        need = "win32com_.gen_py.debugger.dbgpyapp" ∉ sys.modules
    else
        need = 0
    end
    if need
        CreateDefaultGUI(win32com_.gen_py.framework.app, dbgpyapp.DebuggerPythonApp)
    else
        #= pass =#
    end
    return need
end

currentDebugger = nothing
function _GetCurrentDebugger()
    global currentDebugger
    if currentDebugger === nothing
        _CheckNeedGUI()
        currentDebugger = Debugger(debugger)
    end
    return currentDebugger
end

function GetDebugger()
    try
        rc = _GetCurrentDebugger()
        GUICheckInit(rc)
        return rc
    catch exn
        println("Could not create the debugger!")
        current_exceptions() != [] ? current_exceptions()[end] : nothing
        return nothing
    end
end

function close()
    if currentDebugger != nothing
        close()
    end
end

function run(cmd, globals = nothing, locals = nothing, start_stepping = 1)
    run(_GetCurrentDebugger(), cmd, globals, locals)
end

function runeval(expression, globals = nothing, locals = nothing)
    return runeval(_GetCurrentDebugger(), expression, globals)
end

function runcall()
    return runcall()
end

function set_trace()
    d = _GetCurrentDebugger()
    if d.frameShutdown
        return
    end
    if d.stopframe != d.botframe
        return
    end
    settrace(sys, nothing)
    reset(d)
    set_trace()
end

brk = set_trace
function post_mortem(t = nothing)
    if t === nothing
        t = exc_info(sys)[3]
    end
    if t === nothing
        try
            t = sys.last_traceback
        catch exn
            if exn isa AttributeError
                println(
                    "No traceback can be found from which to perform post-mortem debugging!",
                )
                println("No debugging can continue")
                return
            end
        end
    end
    p = _GetCurrentDebugger()
    if p.frameShutdown
        return
    end
    settrace(sys, nothing)
    reset(p)
    while t.tb_next != nothing
        t = t.tb_next
    end
    p.bAtPostMortem = 1
    prep_run(p, nothing)
    try
        interaction(p, t.tb_frame, t)
    finally
        t = nothing
        p.bAtPostMortem = 0
        done_run(p)
    end
end

function pm(t = nothing)
    post_mortem(t)
end
