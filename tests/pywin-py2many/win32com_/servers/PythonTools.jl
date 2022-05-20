using importlib: reload
using win32com_.server.register: RegisterServer, UnregisterServer

abstract type AbstractTools end
mutable struct Tools <: AbstractTools
    _public_methods_::Vector{String}

    Tools(_public_methods_::Vector{String} = ["reload", "adddir", "echo", "sleep"]) =
        new(_public_methods_)
end
function reload(self::Tools, module_)::String
    if module_ ∈ sys.modules
        reload(sys.modules[module_+1])
        return "reload succeeded."
    end
    return "no reload performed."
end

function adddir(self::Tools, dir)::String
    if type_(dir) == type_("")
        append(sys.path, dir)
    end
    return string(sys.path)
end

function echo(self::Tools, arg)
    return repr(arg)
end

function sleep(self::Tools, t)
    sleep(time, t)
end

if abspath(PROGRAM_FILE) == @__FILE__
    clsid = "{06ce7630-1d81-11d0-ae37-c2fa70000000}"
    progid = "Python.Tools"
    verprogid = "Python.Tools.1"
    if "--unregister" ∈ append!([PROGRAM_FILE], ARGS)
        println("Unregistering...")
        UnregisterServer(clsid, progid, verprogid)
        println("Unregistered OK")
    else
        println("Registering COM server...")
        RegisterServer(
            clsid,
            "win32com_.servers.PythonTools.Tools",
            "Python Tools",
            progid,
            verprogid,
        )
        println("Class registered.")
    end
end
