#= Utilities for registering objects.

This module contains utility functions to register Python objects as
valid COM Servers.  The RegisterServer function provides all information
necessary to allow the COM framework to respond to a request for a COM object,
construct the necessary Python object, and dispatch COM events.

 =#
using Printf
using PyCall
pythoncom = pyimport("pythoncom")
win32api = pyimport("win32api")
import win32com_.server
using win32com_.shell.shell: ShellExecuteEx
using win32com_.shell: shellcon
import win32process
import win32event
import winxpgui
import tempfile

import win32con

import winerror

CATID_PythonCOMServer = "{B3EF80D0-68E2-11D0-A689-00C04FD658FF}"
function _set_subkeys(keyName, valueDict, base = win32con.HKEY_CLASSES_ROOT)
    hkey = RegCreateKey(win32api, base, keyName)
    try
        for (key, value) in items(valueDict)
            RegSetValueEx(win32api, hkey, key, nothing, win32con.REG_SZ, value)
        end
    finally
        RegCloseKey(win32api, hkey)
    end
end

function _set_string(path, value, base = win32con.HKEY_CLASSES_ROOT)
    #= Set a string value in the registry. =#
    RegSetValue(win32api, base, path, win32con.REG_SZ, value)
end

function _get_string(path, base = win32con.HKEY_CLASSES_ROOT)
    #= Get a string value from the registry. =#
    try
        return RegQueryValue(win32api, base, path)
    catch exn
        if exn isa win32api.error
            return nothing
        end
    end
end

function _remove_key(path, base = win32con.HKEY_CLASSES_ROOT)
    #= Remove a string from the registry. =#
    try
        RegDeleteKey(win32api, base, path)
    catch exn
        let xxx_todo_changeme1 = exn
            if xxx_todo_changeme1 isa win32api.error
                code, fn, msg = xxx_todo_changeme1.args
                if code != winerror.ERROR_FILE_NOT_FOUND
                    throw(error(win32api, code, fn, msg))
                end
            end
        end
    end
end

function recurse_delete_key(path, base = win32con.HKEY_CLASSES_ROOT)
    #= Recursively delete registry keys.

        This is needed since you can't blast a key when subkeys exist.
         =#
    try
        h = RegOpenKey(win32api, base, path)
    catch exn
        let xxx_todo_changeme2 = exn
            if xxx_todo_changeme2 isa win32api.error
                code, fn, msg = xxx_todo_changeme2.args
                if code != winerror.ERROR_FILE_NOT_FOUND
                    throw(error(win32api, code, fn, msg))
                end
            end
        end
    end
end

function _cat_registrar()
    return CoCreateInstance(
        pythoncom,
        pythoncom.CLSID_StdComponentCategoriesMgr,
        nothing,
        pythoncom.CLSCTX_INPROC_SERVER,
        pythoncom.IID_ICatRegister,
    )
end

function _find_localserver_exe(mustfind)
    if !startswith(sys.platform, "win32")
        return sys.executable
    end
    if find(pythoncom.__file__, "_d") < 0
        exeBaseName = "pythonw.exe"
    else
        exeBaseName = "pythonw_d.exe"
    end
    exeName = join
    if !exists(os.path, exeName)
        exeName = join
    end
    if !exists(os.path, exeName)
        if "64 bit" ∈ sys.version
            exeName = join
        else
            exeName = join
        end
    end
    if !exists(os.path, exeName)
        try
            key = "SOFTWARE\\Python\\PythonCore\\%s\\InstallPath" % sys.winver
            path = RegQueryValue(win32api, win32con.HKEY_LOCAL_MACHINE, key)
            exeName = join
        catch exn
            if exn isa (AttributeError, win32api.error)
                #= pass =#
            end
        end
    end
    if !exists(os.path, exeName)
        if mustfind
            throw(RuntimeError("Can not locate the program \'%s\'" % exeBaseName))
        end
        return nothing
    end
    return exeName
end

function _find_localserver_module()
    path = win32com_.server.__path__[1]
    baseName = "localserver"
    pyfile = join
    try
        stat(os, pyfile)
    catch exn
        if exn isa os.error
            if __debug__
                ext = ".pyc"
            else
                ext = ".pyo"
            end
            pyfile = join
            try
                stat(os, pyfile)
            catch exn
                if exn isa os.error
                    throw(
                        RuntimeError(
                            "Can not locate the Python module \'win32com_.server.%s\'" %
                            baseName,
                        ),
                    )
                end
            end
        end
    end
    return pyfile
end

function RegisterServer(
    clsid,
    pythonInstString = nothing,
    desc = nothing,
    progID = nothing,
    verProgID = nothing,
    defIcon = nothing,
    threadingModel = "both",
    policy = nothing,
    catids = [],
    other = Dict(),
    addPyComCat = nothing,
    dispatcher = nothing,
    clsctx = nothing,
    addnPath = nothing,
)
    #= Registers a Python object as a COM Server.  This enters almost all necessary
        information in the system registry, allowing COM to use the object.

        clsid -- The (unique) CLSID of the server.
        pythonInstString -- A string holding the instance name that will be created
                      whenever COM requests a new object.
        desc -- The description of the COM object.
        progID -- The user name of this object (eg, Word.Document)
        verProgId -- The user name of this version's implementation (eg Word.6.Document)
        defIcon -- The default icon for the object.
        threadingModel -- The threading model this object supports.
        policy -- The policy to use when creating this object.
        catids -- A list of category ID's this object belongs in.
        other -- A dictionary of extra items to be registered.
        addPyComCat -- A flag indicating if the object should be added to the list
                 of Python servers installed on the machine.  If None (the default)
                 then it will be registered when running from python source, but
                 not registered if running in a frozen environment.
        dispatcher -- The dispatcher to use when creating this object.
        clsctx -- One of the CLSCTX_* constants.
        addnPath -- An additional path the COM framework will add to sys.path
                    before attempting to create the object.
         =#
    if !(pythonInstString) && !(policy)
        throw(
            TypeError(
                "You must specify either the Python Class or Python Policy which implement the COM object.",
            ),
        )
    end
    keyNameRoot = "CLSID\\%s" % string(clsid)
    _set_string(keyNameRoot, desc)
    _set_string("AppID\\%s" % clsid, progID)
    if !(clsctx)
        clsctx = pythoncom.CLSCTX_INPROC_SERVER | pythoncom.CLSCTX_LOCAL_SERVER
    end
    if pythoncom.frozen
        @assert(sys.frozen)
        if sys.frozen == "dll"
            clsctx = clsctx & pythoncom.CLSCTX_INPROC_SERVER
        else
            clsctx = clsctx & pythoncom.CLSCTX_LOCAL_SERVER
        end
    end
    if clsctx & pythoncom.CLSCTX_INPROC_SERVER
        if pythoncom.frozen
            if hasfield(typeof(sys), :frozendllhandle)
                dllName = GetModuleFileName(win32api, sys.frozendllhandle)
            else
                throw(
                    RuntimeError(
                        "We appear to have a frozen DLL, but I don\'t know the DLL to use",
                    ),
                )
            end
        else
            pythoncom_dir = dirname(os.path, pythoncom.__file__)
            suffix = "_d" ∈ pythoncom.__file__ ? ("_d") : ("")
            loadername = join
            dllName = isfile(os.path, loadername) ? (loadername) : (pythoncom.__file__)
        end
        _set_subkeys(
            keyNameRoot * "\\InprocServer32",
            Dict(nothing => dllName, "ThreadingModel" => threadingModel),
        )
    else
        _remove_key(keyNameRoot * "\\InprocServer32")
    end
    if clsctx & pythoncom.CLSCTX_LOCAL_SERVER
        if pythoncom.frozen
            exeName = GetShortPathName(win32api, sys.executable)
            command = "%s /Automate" % (exeName,)
        else
            exeName = _find_localserver_exe(1)
            exeName = GetShortPathName(win32api, exeName)
            pyfile = _find_localserver_module()
            command = "%s \"%s\" %s" % (exeName, pyfile, string(clsid))
        end
        _set_string(keyNameRoot * "\\LocalServer32", command)
    else
        _remove_key(keyNameRoot * "\\LocalServer32")
    end
    if pythonInstString
        _set_string(keyNameRoot * "\\PythonCOM", pythonInstString)
    else
        _remove_key(keyNameRoot * "\\PythonCOM")
    end
    if policy
        _set_string(keyNameRoot * "\\PythonCOMPolicy", policy)
    else
        _remove_key(keyNameRoot * "\\PythonCOMPolicy")
    end
    if dispatcher
        _set_string(keyNameRoot * "\\PythonCOMDispatcher", dispatcher)
    else
        _remove_key(keyNameRoot * "\\PythonCOMDispatcher")
    end
    if defIcon
        _set_string(keyNameRoot * "\\DefaultIcon", defIcon)
    else
        _remove_key(keyNameRoot * "\\DefaultIcon")
    end
    if addnPath
        _set_string(keyNameRoot * "\\PythonCOMPath", addnPath)
    else
        _remove_key(keyNameRoot * "\\PythonCOMPath")
    end
    if addPyComCat === nothing
        addPyComCat = pythoncom.frozen == 0
    end
    if addPyComCat
        catids = append!(catids, [CATID_PythonCOMServer])
    end
    if catids
        regCat = _cat_registrar()
        RegisterClassImplCategories(regCat, clsid, catids)
    end
    if other
        for (key, value) in items(other)
            _set_string(keyNameRoot * "\\" + key, value)
        end
    end
    if progID
        if verProgID
            _set_string(keyNameRoot * "\\ProgID", verProgID)
        else
            _set_string(keyNameRoot * "\\ProgID", progID)
        end
        if desc
            _set_string(progID, desc)
        end
        _set_string(progID + "\\CLSID", string(clsid))
        if verProgID
            _set_string(progID + "\\CurVer", verProgID)
            _set_string(keyNameRoot * "\\VersionIndependentProgID", progID)
            if desc
                _set_string(verProgID, desc)
            end
            _set_string(verProgID + "\\CLSID", string(clsid))
        end
    end
end

function GetUnregisterServerKeys(
    clsid,
    progID = nothing,
    verProgID = nothing,
    customKeys = nothing,
)
    #= Given a server, return a list of of ("key", root), which are keys recursively
        and uncondtionally deleted at unregister or uninstall time.
         =#
    ret = [("CLSID\\%s" % string(clsid), win32con.HKEY_CLASSES_ROOT)]
    if verProgID
        push!(ret, (verProgID, win32con.HKEY_CLASSES_ROOT))
    end
    if progID
        push!(ret, (progID, win32con.HKEY_CLASSES_ROOT))
    end
    push!(ret, ("AppID\\%s" % string(clsid), win32con.HKEY_CLASSES_ROOT))
    if customKeys
        ret = ret + customKeys
    end
    return ret
end

function UnregisterServer(
    clsid,
    progID = nothing,
    verProgID = nothing,
    customKeys = nothing,
)
    #= Unregisters a Python COM server. =#
    for args in GetUnregisterServerKeys(clsid, progID, verProgID, customKeys)
        recurse_delete_key(args...)
    end
end

function GetRegisteredServerOption(clsid, optionName)
    #= Given a CLSID for a server and option name, return the option value =#
    keyNameRoot = "CLSID\\%s\\%s" % (string(clsid), string(optionName))
    return _get_string(keyNameRoot)
end

function _get(ob, attr, default = nothing)
    try
        return getfield(ob, :attr)
    catch exn
        if exn isa AttributeError
            #= pass =#
        end
    end
    try
        bases = ob.__bases__
    catch exn
        if exn isa AttributeError
            return default
        end
    end
    for base in bases
        val = _get(base, attr, nothing)
        if val != nothing
            return val
        end
    end
    return default
end

function RegisterClasses()
    quiet = "quiet" ∈ flags && flags["quiet"]
    debugging = "debug" ∈ flags && flags["debug"]
    for cls in classes
        clsid = cls._reg_clsid_
        progID = _get(cls, "_reg_progid_")
        desc = _get(cls, "_reg_desc_", progID)
        spec = _get(cls, "_reg_class_spec_")
        verProgID = _get(cls, "_reg_verprogid_")
        defIcon = _get(cls, "_reg_icon_")
        threadingModel = _get(cls, "_reg_threading_", "both")
        catids = _get(cls, "_reg_catids_", [])
        options = _get(cls, "_reg_options_", Dict())
        policySpec = _get(cls, "_reg_policy_spec_")
        clsctx = _get(cls, "_reg_clsctx_")
        tlb_filename = _get(cls, "_reg_typelib_filename_")
        addPyComCat = !_get(cls, "_reg_disable_pycomcat_", pythoncom.frozen != 0)
        addnPath = nothing
        if debugging
            dispatcherSpec = _get(cls, "_reg_debug_dispatcher_spec_")
            if dispatcherSpec === nothing
                dispatcherSpec = "win32com_.server.dispatcher.DefaultDebugDispatcher"
            end
            debuggingDesc = "(for debugging)"
            options["Debugging"] = "1"
        else
            dispatcherSpec = _get(cls, "_reg_dispatcher_spec_")
            debuggingDesc = ""
            options["Debugging"] = "0"
        end
        if spec === nothing
            moduleName = cls.__module__
            if moduleName == "__main__"
                try
                    moduleName = splitext(
                        os.path,
                        FindFiles(win32api, append!([PROGRAM_FILE], ARGS)[1])[1][9],
                    )[1]
                catch exn
                    if exn isa (IndexError, win32api.error)
                        throw(
                            TypeError(
                                "Can\'t locate the script hosting the COM object - please set _reg_class_spec_ in your object",
                            ),
                        )
                    end
                end
            end
            spec = (moduleName + ".") + cls.__name__
            if !(pythoncom.frozen)
                scriptDir = split(os.path, append!([PROGRAM_FILE], ARGS)[1])[1]
                if !(scriptDir)
                    scriptDir = "."
                end
                addnPath = GetFullPathName(win32api, scriptDir)
            end
        end
        RegisterServer(
            clsid,
            spec,
            desc,
            progID,
            verProgID,
            defIcon,
            threadingModel,
            policySpec,
            catids,
            options,
            addPyComCat,
            dispatcherSpec,
            clsctx,
            addnPath,
        )
        if !(quiet)
            println("Registered:$(progID || spec)$(debuggingDesc)")
        end
        if tlb_filename
            tlb_filename = abspath(os.path, tlb_filename)
            typelib = LoadTypeLib(pythoncom, tlb_filename)
            RegisterTypeLib(pythoncom, typelib, tlb_filename)
            if !(quiet)
                println("Registered type library:$(tlb_filename)")
            end
        end
    end
    extra = get(flags, "finalize_register")
    if extra
        extra()
    end
end

function UnregisterClasses()
    quiet = "quiet" ∈ flags && flags["quiet"]
    for cls in classes
        clsid = cls._reg_clsid_
        progID = _get(cls, "_reg_progid_")
        verProgID = _get(cls, "_reg_verprogid_")
        customKeys = _get(cls, "_reg_remove_keys_")
        unregister_typelib = _get(cls, "_reg_typelib_filename_") != nothing
        UnregisterServer(clsid, progID, verProgID, customKeys)
        if !(quiet)
            println("Unregistered:$(progID || string(clsid))")
        end
        if unregister_typelib
            tlb_guid = _get(cls, "_typelib_guid_")
            if tlb_guid === nothing
                println("Have typelib filename, but no GUID - can\'t unregister")
            else
                major, minor = _get(cls, "_typelib_version_", (1, 0))
                lcid = _get(cls, "_typelib_lcid_", 0)
                try
                    UnRegisterTypeLib(pythoncom, tlb_guid, major, minor, lcid)
                    if !(quiet)
                        println("Unregistered type library")
                    end
                catch exn
                    if exn isa pythoncom.com_error
                        #= pass =#
                    end
                end
            end
        end
    end
    extra = get(flags, "finalize_unregister")
    if extra
        extra()
    end
end

function UnregisterInfoClasses()::Vector
    ret = []
    for cls in classes
        clsid = cls._reg_clsid_
        progID = _get(cls, "_reg_progid_")
        verProgID = _get(cls, "_reg_verprogid_")
        customKeys = _get(cls, "_reg_remove_keys_")
        ret = ret + GetUnregisterServerKeys(clsid, progID, verProgID, customKeys)
    end
    return ret
end

function ReExecuteElevated(flags)
    if !(flags["quiet"])
        println("Requesting elevation and retrying...")
    end
    new_params = join([("\"" + a) * "\"" for a in append!([PROGRAM_FILE], ARGS)], " ")
    if !(flags["unattended"])
        new_params += " --unattended"
    end
    hwnd = get(flags, "hwnd", nothing)
    if hwnd === nothing
        try
            hwnd = GetConsoleWindow(winxpgui)
        catch exn
            if exn isa winxpgui.error
                hwnd = 0
            end
        end
    end
    tempbase = mktemp(tempfile, "pycomserverreg")
    outfile = tempbase + ".out"
    batfile = tempbase + ".bat"
    current_exe = lower(split(os.path, sys.executable)[2])
    exe_to_run = nothing
    if current_exe == "pythonwin.exe"
        exe_to_run = join
    elseif current_exe == "pythonwin_d.exe"
        exe_to_run = join
    end
    if !(exe_to_run) || !exists(os.path, exe_to_run)
        exe_to_run = sys.executable
    end
    try
        batf = readline(batfile)
        try
            cwd = getcwd(os)
            write(batf, "@echo off")
            write(batf, "$(get(os.environ, "PYTHONPATH", ""))")
            write(batf, "$(splitdrive(os.path, cwd)[1])")
            write(batf, "$(getcwd(os))\"")
            write(batf, "$(GetShortPathName(win32api, exe_to_run)) $(new_params)\" 2>&1")
        finally
            close(batf)
        end
        executable = get(os.environ, "COMSPEC", "cmd.exe")
        rc = ShellExecuteEx(
            hwnd,
            shellcon.SEE_MASK_NOCLOSEPROCESS,
            "runas",
            executable,
            "/C \"%s\"" % batfile,
            win32con.SW_SHOW,
        )
        hproc = rc["hProcess"]
        WaitForSingleObject(win32event, hproc, win32event.INFINITE)
        exit_code = GetExitCodeProcess(win32process, hproc)
        outf = readline(outfile)
        try
            output = read(outf)
        finally
            close(outf)
        end
        if exit_code
            @printf("Error: registration failed (exit code %s).\n", exit_code)
        end
        print("$(output)")
    finally
        for f in (outfile, batfile)
            try
                std::fs::remove_file(f)
            catch exn
                let exc = exn
                    if exc isa os.error
                        @printf("Failed to remove tempfile \'%s\': %s\n", f, exc)
                    end
                end
            end
        end
    end
end

function UseCommandLine()::Vector
    unregisterInfo = "--unregister_info" ∈ append!([PROGRAM_FILE], ARGS)
    unregister = "--unregister" ∈ append!([PROGRAM_FILE], ARGS)
    flags["quiet"] = get(flags, "quiet", 0) || "--quiet" ∈ append!([PROGRAM_FILE], ARGS)
    flags["debug"] = get(flags, "debug", 0) || "--debug" ∈ append!([PROGRAM_FILE], ARGS)
    flags["unattended"] =
        get(flags, "unattended", 0) || "--unattended" ∈ append!([PROGRAM_FILE], ARGS)
    if unregisterInfo
        return UnregisterInfoClasses()
    end
    try
        if unregister
            UnregisterClasses()
        else
            RegisterClasses()
        end
    catch exn
        let exc = exn
            if exc isa win32api.error
                if flags["unattended"] ||
                   exc.winerror != winerror.ERROR_ACCESS_DENIED ||
                   getwindowsversion(sys)[1] < 5
                    error()
                end
                ReExecuteElevated(flags)
            end
        end
    end
end

function RegisterPyComCategory()
    #= Register the Python COM Server component category. =#
    regCat = _cat_registrar()
    RegisterCategories(regCat, [(CATID_PythonCOMServer, 1033, "Python COM Server")])
end

if !(pythoncom.frozen)
    try
        RegQueryValue(
            win32api,
            win32con.HKEY_CLASSES_ROOT,
            "Component Categories\\%s" % CATID_PythonCOMServer,
        )
    catch exn
        if exn isa win32api.error
            try
                RegisterPyComCategory()
            catch exn
                if exn isa pythoncom.error
                    #= pass =#
                end
            end
        end
    end
end
