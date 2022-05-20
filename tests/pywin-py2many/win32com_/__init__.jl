using PyCall
pythoncom = pyimport("pythoncom")
win32api = pyimport("win32api")
import win32com_.gen_py

_frozen = (hasfield(typeof(sys), :frozen) ? getfield(sys, :frozen) : 1 == 0)
if _frozen && !(hasfield(typeof(pythoncom), :frozen) ? getfield(pythoncom, :frozen) : 0)
    pythoncom.frozen = sys.frozen
end
__gen_path__ = ""
__build_path__ = nothing
function SetupEnvironment()
    HKEY_LOCAL_MACHINE = -2147483646
    KEY_QUERY_VALUE = 1
    try
        keyName = "SOFTWARE\\Python\\PythonCore\\%s\\PythonPath\\win32com_" % sys.winver
        key = RegOpenKey(win32api, HKEY_LOCAL_MACHINE, keyName, 0, KEY_QUERY_VALUE)
    catch exn
        if exn isa (win32api.error, AttributeError)
            key = nothing
        end
    end
    try
        found = 0
        if key != nothing
            try
                append(__path__, RegQueryValue(win32api, key, "Extensions"))
                found = 1
            catch exn
                if exn isa win32api.error
                    #= pass =#
                end
            end
        end
        if !(found) != 0
            try
                append(
                    __path__,
                    GetFullPathName(win32api, __path__[1] + "\\..\\win32comext"),
                )
            catch exn
                if exn isa win32api.error
                    #= pass =#
                end
            end
        end
        try
            if key != nothing
                global __build_path__
                __build_path__ = RegQueryValue(win32api, key, "BuildPath")
                append(__path__, __build_path__)
            end
        catch exn
            if exn isa win32api.error
                #= pass =#
            end
        end
        global __gen_path__
        if key != nothing
            try
                __gen_path__ = RegQueryValue(win32api, key, "GenPath")
            catch exn
                if exn isa win32api.error
                    #= pass =#
                end
            end
        end
    finally
        if key != nothing
            Close(key)
        end
    end
end

function __PackageSupportBuildPath__(package_path)
    if !(_frozen) && __build_path__
        append(package_path, __build_path__)
    end
end

if !(_frozen)
    SetupEnvironment()
end
if !(__gen_path__)
    try
    catch exn
        if exn isa ImportError
            __gen_path__ = abspath(os.path, join)
            if !isdir(os.path, __gen_path__)
                __gen_path__ = join
            end
        end
    end
end
if "win32com_.gen_py" ∉ sys.modules
    gen_py = ModuleType(types, "win32com_.gen_py")
    gen_py.__path__ = [__gen_path__]
    sys.modules[gen_py.__name__+1] = gen_py
    #Delete Unsupported
    del(types)
end
gen_py = sys.modules["win32com_.gen_py"]
#Delete Unsupported
del(pythoncom)
