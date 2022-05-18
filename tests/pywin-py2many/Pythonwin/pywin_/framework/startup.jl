#= The main application startup code for PythonWin. =#
using PyCall
win32ui = pyimport("win32ui")
win32api = pyimport("win32api")
include("cmdline.jl")




if !(append!([PROGRAM_FILE], ARGS))
argv = CommandLineToArgv(win32api, GetCommandLine(win32api))
append!([PROGRAM_FILE], ARGS) = argv[2:end]
if getcwd(os) ∉ sys.path && "." ∉ sys.path
insert(sys.path, 0, getcwd(os))
end
end
import win32com_.gen_py
import win32com_.gen_py.framework
win32com_.gen_py.__path__[1] = FullPath(win32ui, win32com_.gen_py.__path__[1])
win32com_.gen_py.framework.__path__[1] = FullPath(win32ui, win32com_.gen_py.framework.__path__[1])
moduleName = "win32com_.gen_py.framework.intpyapp"
sys.appargvoffset = 0
sys.appargv = append!([PROGRAM_FILE], ARGS)[begin:end]
if length(append!([PROGRAM_FILE], ARGS)) >= 2 && lower(append!([PROGRAM_FILE], ARGS)[1]) ∈ ("/app", "-app")
moduleName = FixArgFileName(cmdline, append!([PROGRAM_FILE], ARGS)[2])
sys.appargvoffset = 2
newargv = append!([PROGRAM_FILE], ARGS)[sys.appargvoffset + 1:end]
append!([PROGRAM_FILE], ARGS) = newargv
end
__import__(moduleName)
try
GetApp(win32ui)._obj_
catch exn
if exn isa (AttributeError, win32ui.error)
include("app.jl")
if app.AppBuilder === nothing
throw(TypeError("No application object has been registered"))
end
app.App = AppBuilder(app)
end
end