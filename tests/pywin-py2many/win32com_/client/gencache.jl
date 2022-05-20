#= Manages the cache of generated Python code.

Description
  This file manages the cache of generated Python code.  When run from the
  command line, it also provides a number of options for managing that cache.

Implementation
  Each typelib is generated into a filename of format "{guid}x{lcid}x{major}x{minor}.py"

  An external persistant dictionary maps from all known IIDs in all known type libraries
  to the type library itself.

  Thus, whenever Python code knows the IID of an object, it can find the IID, LCID and version of
  the type library which supports it.  Given this information, it can find the Python module
  with the support.

  If necessary, this support can be generated on the fly.

Hacks, to do, etc
  Currently just uses a pickled dictionary, but should used some sort of indexed file.
  Maybe an OLE2 compound file, or a bsddb file?
 =#
using Getopt
using OrderedCollections
using Printf
using PyCall
using StringEncodings
using ZipFile
pythoncom = pyimport("pythoncom")
pywintypes = pyimport("pywintypes")
import io as io
include("makepy.jl")
include("genpy.jl")
import shutil
import zipfile
import getopt

import glob
include("CLSIDToClass.jl")
using importlib: reload
import win32com_
import win32com_.client
bForDemandDefault = 0
clsidToTypelib = OrderedDict()
versionRedirectMap = Dict()
is_readonly =
    hasfield(typeof(win32com_), :__loader__) &&
    hasfield(typeof(win32com_.__loader__), :archive)
is_zip =
    hasfield(typeof(win32com_), :__loader__) &&
    hasfield(typeof(win32com_.__loader__), :archive)
demandGeneratedTypeLibraries = Dict()

function __init__()
    try
        _LoadDicts()
    catch exn
        if exn isa IOError
            Rebuild()
        end
    end
end

pickleVersion = 1
function _SaveDicts()
    if is_readonly
        throw(
            RuntimeError(
                "Trying to write to a readonly gencache (\'%s\')!" % win32com_.__gen_path__,
            ),
        )
    end
    f = readline(join)
    try
        p = Pickler(pickle, f)
        dump(p, pickleVersion)
        dump(p, clsidToTypelib)
    finally
        close(f)
    end
end

function _LoadDicts()
    if is_zip
        loader = win32com_.__loader__
        arc_path = loader.archive
        dicts_path = join
        if startswith(dicts_path, arc_path)
            dicts_path = dicts_path[length(arc_path)+2:end]
        else
            return
        end
        try
            data = get_data(loader, dicts_path)
        catch exn
            if exn isa AttributeError
                return
            end
            if exn isa IOError
                return
            end
        end
        f = BytesIO(io, data)
    else
        f = readline(join)
    end
    try
        p = Unpickler(pickle, f)
        version = load(p)
        global clsidToTypelib
        clsidToTypelib = load(p)
        clear(versionRedirectMap)
    finally
        close(f)
    end
end

function GetGeneratedFileName(clsid, lcid, major, minor)::Any
    #= Given the clsid, lcid, major and  minor for a type lib, return
        the file name (no extension) providing this support.
         =#
    return upper(string(clsid))[2:-1] + ("x%sx%sx%s" % (lcid, major, minor))
end

function SplitGeneratedFileName(fname)::Tuple
    #= Reverse of GetGeneratedFileName() =#
    return tuple(split(fname, "x", 4))
end

function GetGeneratePath()
    #= Returns the name of the path to generate to.
        Checks the directory is OK.
         =#
    @assert(!(is_readonly))
    try
        makedirs(os, win32com_.__gen_path__)
    catch exn
        if exn isa os.error
            #= pass =#
        end
    end
    try
        fname = join
        stat(os, fname)
    catch exn
        if exn isa os.error
            f = readline(fname)
            write(
                f,
                "# Generated file - this directory may be deleted to reset the COM cache...\n",
            )
            write(f, "import win32com_\n")
            write(
                f,
                "if __path__[:-1] != win32com_.__gen_path__: __path__.append(win32com_.__gen_path__)\n",
            )
            close(f)
        end
    end
    return win32com_.__gen_path__
end

function GetClassForProgID(progid)
    #= Get a Python class for a Program ID

        Given a Program ID, return a Python class which wraps the COM object

        Returns the Python class, or None if no module is available.

        Params
        progid -- A COM ProgramID or IID (eg, "Word.Application")
         =#
    clsid = IID(pywintypes, progid)
    return GetClassForCLSID(clsid)
end

function GetClassForCLSID(clsid)
    #= Get a Python class for a CLSID

        Given a CLSID, return a Python class which wraps the COM object

        Returns the Python class, or None if no module is available.

        Params
        clsid -- A COM CLSID (or string repr of one)
         =#
    clsid = string(clsid)
    if HasClass(CLSIDToClass, clsid)
        return GetClass(CLSIDToClass, clsid)
    end
    mod = GetModuleForCLSID(clsid)
    if mod === nothing
        return nothing
    end
    try
        return GetClass(CLSIDToClass, clsid)
    catch exn
        if exn isa KeyError
            return nothing
        end
    end
end

function GetModuleForProgID(progid)
    #= Get a Python module for a Program ID

        Given a Program ID, return a Python module which contains the
        class which wraps the COM object.

        Returns the Python module, or None if no module is available.

        Params
        progid -- A COM ProgramID or IID (eg, "Word.Application")
         =#
    try
        iid = IID(pywintypes, progid)
    catch exn
        if exn isa pywintypes.com_error
            return nothing
        end
    end
    return GetModuleForCLSID(iid)
end

function GetModuleForCLSID(clsid)
    #= Get a Python module for a CLSID

        Given a CLSID, return a Python module which contains the
        class which wraps the COM object.

        Returns the Python module, or None if no module is available.

        Params
        progid -- A COM CLSID (ie, not the description)
         =#
    clsid_str = string(clsid)
    try
        typelibCLSID, lcid, major, minor = clsidToTypelib[clsid_str]
    catch exn
        if exn isa KeyError
            return nothing
        end
    end
    try
        mod = GetModuleForTypelib(typelibCLSID, lcid, major, minor)
    catch exn
        if exn isa ImportError
            mod = nothing
        end
    end
    if mod != nothing
        sub_mod = get(mod.CLSIDToPackageMap, clsid_str)
        if sub_mod === nothing
            sub_mod = get(mod.VTablesToPackageMap, clsid_str)
        end
        if sub_mod != nothing
            sub_mod_name = (mod.__name__ + ".") + sub_mod
            try
                __import__(sub_mod_name)
            catch exn
                if exn isa ImportError
                    info = (typelibCLSID, lcid, major, minor)
                    if info ∈ demandGeneratedTypeLibraries
                        info = demandGeneratedTypeLibraries[info]
                    end
                    GenerateChildFromTypeLibSpec(makepy, sub_mod, info)
                end
            end
            mod = sys.modules[sub_mod_name+1]
        end
    end
    return mod
end

function GetModuleForTypelib(typelibCLSID, lcid, major, minor)
    #= Get a Python module for a type library ID

        Given the CLSID of a typelibrary, return an imported Python module,
        else None

        Params
        typelibCLSID -- IID of the type library.
        major -- Integer major version.
        minor -- Integer minor version
        lcid -- Integer LCID for the library.
         =#
    modName = GetGeneratedFileName(typelibCLSID, lcid, major, minor)
    mod = _GetModule(modName)
    if "_in_gencache_" ∉ mod.__dict__
        AddModuleToCache(typelibCLSID, lcid, major, minor)
        @assert("_in_gencache_" ∈ mod.__dict__)
    end
    return mod
end

function MakeModuleForTypelib(
    typelibCLSID,
    lcid,
    major,
    minor,
    progressInstance = nothing,
    bForDemand = bForDemandDefault,
    bBuildHidden = 1,
)
    #= Generate support for a type library.

        Given the IID, LCID and version information for a type library, generate
        and import the necessary support files.

        Returns the Python module.  No exceptions are caught.

        Params
        typelibCLSID -- IID of the type library.
        major -- Integer major version.
        minor -- Integer minor version.
        lcid -- Integer LCID for the library.
        progressInstance -- Instance to use as progress indicator, or None to
                            use the GUI progress bar.
         =#
    GenerateFromTypeLibSpec(
        makepy,
        (typelibCLSID, lcid, major, minor),
        progressInstance,
        bForDemand,
        bBuildHidden,
    )
    return GetModuleForTypelib(typelibCLSID, lcid, major, minor)
end

function MakeModuleForTypelibInterface(
    typelib_ob,
    progressInstance = nothing,
    bForDemand = bForDemandDefault,
    bBuildHidden = 1,
)
    #= Generate support for a type library.

        Given a PyITypeLib interface generate and import the necessary support files.  This is useful
        for getting makepy support for a typelibrary that is not registered - the caller can locate
        and load the type library itself, rather than relying on COM to find it.

        Returns the Python module.

        Params
        typelib_ob -- The type library itself
        progressInstance -- Instance to use as progress indicator, or None to
                            use the GUI progress bar.
         =#
    try
        GenerateFromTypeLibSpec(
            makepy,
            typelib_ob,
            progressInstance,
            bForDemandDefault,
            bBuildHidden,
        )
    catch exn
        if exn isa pywintypes.com_error
            return nothing
        end
    end
    tla = GetLibAttr(typelib_ob)
    guid = tla[1]
    lcid = tla[2]
    major = tla[4]
    minor = tla[5]
    return GetModuleForTypelib(guid, lcid, major, minor)
end

function EnsureModuleForTypelibInterface(
    typelib_ob,
    progressInstance = nothing,
    bForDemand = bForDemandDefault,
    bBuildHidden = 1,
)
    #= Check we have support for a type library, generating if not.

        Given a PyITypeLib interface generate and import the necessary
        support files if necessary. This is useful for getting makepy support
        for a typelibrary that is not registered - the caller can locate and
        load the type library itself, rather than relying on COM to find it.

        Returns the Python module.

        Params
        typelib_ob -- The type library itself
        progressInstance -- Instance to use as progress indicator, or None to
                            use the GUI progress bar.
         =#
    tla = GetLibAttr(typelib_ob)
    guid = tla[1]
    lcid = tla[2]
    major = tla[4]
    minor = tla[5]
    if bForDemand
        demandGeneratedTypeLibraries[(string(guid), lcid, major, minor)] = typelib_ob
    end
    try
        return GetModuleForTypelib(guid, lcid, major, minor)
    catch exn
        if exn isa ImportError
            #= pass =#
        end
    end
    return MakeModuleForTypelibInterface(
        typelib_ob,
        progressInstance,
        bForDemand,
        bBuildHidden,
    )
end

function ForgetAboutTypelibInterface(typelib_ob)
    #= Drop any references to a typelib previously added with EnsureModuleForTypelibInterface and forDemand =#
    tla = GetLibAttr(typelib_ob)
    guid = tla[1]
    lcid = tla[2]
    major = tla[4]
    minor = tla[5]
    info = (string(guid), lcid, major, minor)
    try
        delete!(demandGeneratedTypeLibraries, info)
    catch exn
        if exn isa KeyError
            @printf(
                "ForgetAboutTypelibInterface:: Warning - type library with info %s is not being remembered!\n",
                info
            )
        end
    end
    for (key, val) in collect(collect(versionRedirectMap))
        if val == info
            delete!(versionRedirectMap, key)
        end
    end
end

function EnsureModule(
    typelibCLSID,
    lcid,
    major,
    minor,
    progressInstance = nothing,
    bValidateFile = !(is_readonly),
    bForDemand = bForDemandDefault,
    bBuildHidden = 1,
)::Dict
    #= Ensure Python support is loaded for a type library, generating if necessary.

        Given the IID, LCID and version information for a type library, check and if
        necessary (re)generate, then import the necessary support files. If we regenerate the file, there
        is no way to totally snuff out all instances of the old module in Python, and thus we will regenerate the file more than necessary,
        unless makepy/genpy is modified accordingly.

        Returns the Python module.  No exceptions are caught during the generate process.

        Params
        typelibCLSID -- IID of the type library.
        major -- Integer major version.
        minor -- Integer minor version
        lcid -- Integer LCID for the library.
        progressInstance -- Instance to use as progress indicator, or None to
                            use the GUI progress bar.
        bValidateFile -- Whether or not to perform cache validation or not
        bForDemand -- Should a complete generation happen now, or on demand?
        bBuildHidden -- Should hidden members/attributes etc be generated?
         =#
    bReloadNeeded = 0
    try
        try
            module_ = GetModuleForTypelib(typelibCLSID, lcid, major, minor)
        catch exn
            if exn isa ImportError
                module_ = nothing
                try
                    tlbAttr = GetLibAttr(
                        LoadRegTypeLib(pythoncom, typelibCLSID, major, minor, lcid),
                    )
                    if tlbAttr[2] != lcid || tlbAttr[5] != minor
                        try
                            module_ = GetModuleForTypelib(
                                typelibCLSID,
                                tlbAttr[2],
                                tlbAttr[4],
                                tlbAttr[5],
                            )
                        catch exn
                            if exn isa ImportError
                                minor = tlbAttr[5]
                            end
                        end
                    end
                catch exn
                    if exn isa pythoncom.com_error
                        #= pass =#
                    end
                end
            end
        end
        if module_ != nothing && bValidateFile
            @assert(!(is_readonly))
            try
                typLibPath =
                    QueryPathOfRegTypeLib(pythoncom, typelibCLSID, major, minor, lcid)
                if typLibPath[end] == "\000"
                    typLibPath = typLibPath[begin:-1]
                end
                suf = (
                    hasfield(typeof(os.path), :supports_unicode_filenames) ?
                    getfield(os.path, :supports_unicode_filenames) : 0
                )
                if !(suf)
                    try
                        typLibPath = encode(typLibPath, getfilesystemencoding(sys))
                    catch exn
                        if exn isa AttributeError
                            typLibPath = string(typLibPath)
                        end
                    end
                end
                tlbAttributes =
                    GetLibAttr(LoadRegTypeLib(pythoncom, typelibCLSID, major, minor, lcid))
            catch exn
                if exn isa pythoncom.com_error
                    bValidateFile = 0
                end
            end
        end
        if module_ != nothing && bValidateFile
            @assert(!(is_readonly))
            filePathPrefix =
                "%s\\%s" %
                (GetGeneratePath(), GetGeneratedFileName(typelibCLSID, lcid, major, minor))
            filePath = filePathPrefix + ".py"
            filePathPyc = filePathPrefix + ".py"
            if __debug__
                filePathPyc = filePathPyc * "c"
            else
                filePathPyc = filePathPyc * "o"
            end
            if module_.MinorVersion != tlbAttributes[5] ||
               genpy.makepy_version != module_.makepy_version
                try
                    std::fs::remove_file(filePath)
                catch exn
                    if exn isa os.error
                        #= pass =#
                    end
                end
                try
                    std::fs::remove_file(filePathPyc)
                catch exn
                    if exn isa os.error
                        #= pass =#
                    end
                end
                if isdir(os.path, filePathPrefix)
                    rmtree(shutil, filePathPrefix)
                end
                minor = tlbAttributes[5]
                module_ = nothing
                bReloadNeeded = 1
            else
                minor = module_.MinorVersion
                filePathPrefix =
                    "%s\\%s" % (
                        GetGeneratePath(),
                        GetGeneratedFileName(typelibCLSID, lcid, major, minor),
                    )
                filePath = filePathPrefix + ".py"
                filePathPyc = filePathPrefix + ".pyc"
                fModTimeSet = 0
                try
                    pyModTime = stat(os, filePath)[9]
                    fModTimeSet = 1
                catch exn
                    let e = exn
                        if e isa os.error
                            try
                                pyModTime = stat(os, filePathPyc)[9]
                                fModTimeSet = 1
                            catch exn
                                let e = exn
                                    if e isa os.error
                                        #= pass =#
                                    end
                                end
                            end
                        end
                    end
                end
                typLibModTime = stat(os, typLibPath)[9]
                if fModTimeSet && typLibModTime > pyModTime
                    bReloadNeeded = 1
                    module_ = nothing
                end
            end
        end
    catch exn
        if exn isa (ImportError, os.error)
            module_ = nothing
        end
    end
    if module_ === nothing
        if is_readonly
            key = (string(typelibCLSID), lcid, major, minor)
            try
                return versionRedirectMap[key]
            catch exn
                if exn isa KeyError
                    #= pass =#
                end
            end
            items = []
            for desc in GetGeneratedInfos()
                if key[1] == desc[1] && key[2] == desc[2] && key[3] == desc[3]
                    push!(items, desc)
                end
            end
            if items
                sort(items)
                new_minor = items[end][4]
                ret = GetModuleForTypelib(typelibCLSID, lcid, major, new_minor)
            else
                ret = nothing
            end
            versionRedirectMap[key] = ret
            return ret
        end
        module_ = MakeModuleForTypelib(typelibCLSID, lcid, major, minor, progressInstance)
        if bReloadNeeded != 0
            module_ = reload(module_)
            AddModuleToCache(typelibCLSID, lcid, major, minor)
        end
    end
    return module_
end

function EnsureDispatch(prog_id, bForDemand = 1)
    #= Given a COM prog_id, return an object that is using makepy support, building if necessary =#
    disp = Dispatch(win32com_.client, prog_id)
    if !get(disp.__dict__, "CLSID")
        try
            ti = GetTypeInfo(disp._oleobj_)
            disp_clsid = GetTypeAttr(ti)[1]
            tlb, index = GetContainingTypeLib(ti)
            tla = GetLibAttr(tlb)
            mod = EnsureModule(tla[1], tla[2], tla[4], tla[5])
            GetModuleForCLSID(disp_clsid)
            disp_class = GetClassForCLSID(disp_clsid)
            if disp_class
                disp_class = GetClass(CLSIDToClass, string(disp_clsid))
                disp = disp_class(disp._oleobj_)
            end
        catch exn
            if exn isa pythoncom.com_error
                throw(
                    TypeError(
                        "This COM object can not automate the makepy process - please run makepy manually for this object",
                    ),
                )
            end
        end
    end
    return disp
end

function AddModuleToCache(
    typelibclsid,
    lcid,
    major,
    minor,
    verbose = 1,
    bFlushNow = !(is_readonly),
)
    #= Add a newly generated file to the cache dictionary. =#
    fname = GetGeneratedFileName(typelibclsid, lcid, major, minor)
    mod = _GetModule(fname)
    mod._in_gencache_ = 1
    info = (string(typelibclsid), lcid, major, minor)
    dict_modified = false
    function SetTypelibForAllClsids(dict)
        # Not Supported
        # nonlocal dict_modified
        for (clsid, cls) in items(dict)
            if get(clsidToTypelib, clsid) != info
                clsidToTypelib[clsid] = info
                dict_modified = true
            end
        end
    end

    SetTypelibForAllClsids(mod.CLSIDToClassMap)
    SetTypelibForAllClsids(mod.CLSIDToPackageMap)
    SetTypelibForAllClsids(mod.VTablesToClassMap)
    SetTypelibForAllClsids(mod.VTablesToPackageMap)
    if info ∈ versionRedirectMap
        delete!(versionRedirectMap, info)
    end
    if bFlushNow && dict_modified
        _SaveDicts()
    end
end

function GetGeneratedInfos()::Union[Union[Union[list, List], list], List]
    zip_pos = find(win32com_.__gen_path__, ".zip\\")
    if zip_pos >= 0
        zip_file = win32com_.__gen_path__[begin:zip_pos+4]
        zip_path = replace(win32com_.__gen_path__[zip_pos+6:end], "\\", "/")
        zf = ZipFile(zipfile, zip_file)
        infos = Dict()
        for n in namelist(zf)
            if !startswith(n, zip_path)
                continue
            end
            base = split(n[length(zip_path)+2:end], "/")[1]
            try
                iid, lcid, major, minor = split(base, "x")
                lcid = Int(lcid)
                major = Int(major)
                minor = Int(minor)
                iid = IID(pywintypes, ("{" + iid) * "}")
            catch exn
                if exn isa ValueError
                    continue
                end
                if exn isa pywintypes.com_error
                    continue
                end
            end
            infos[(iid, lcid, major, minor)] = 1
        end
        close(zf)
        return collect(keys(infos))
    else
        files = glob(glob, win32com_.__gen_path__ + "\\*")
        ret = []
        for file in files
            if !isdir(os.path, file) && !(splitext(os.path, file)[2] == ".py")
                continue
            end
            name = splitext(os.path, split(os.path, file)[2])[1]
            try
                iid, lcid, major, minor = split(name, "x")
                iid = IID(pywintypes, ("{" + iid) * "}")
                lcid = Int(lcid)
                major = Int(major)
                minor = Int(minor)
            catch exn
                if exn isa ValueError
                    continue
                end
                if exn isa pywintypes.com_error
                    continue
                end
            end
            push!(ret, (iid, lcid, major, minor))
        end
        return ret
    end
end

function _GetModule(fname)
    #= Given the name of a module in the gen_py directory, import and return it. =#
    mod_name = "win32com_.gen_py.%s" % fname
    mod = __import__(mod_name)
    return sys.modules[mod_name+1]
end

function Rebuild(verbose = 1)
    #= Rebuild the cache indexes from the file system. =#
    clear(clsidToTypelib)
    infos = GetGeneratedInfos()
    if verbose && length(infos)
        println("Rebuilding cache of generated files for COM support...")
    end
    for info in infos
        iid, lcid, major, minor = info
        if verbose
            println("Checking$(GetGeneratedFileName(info...))")
        end
        try
            AddModuleToCache(iid, lcid, major, minor, verbose, 0)
        catch exn
            @printf(
                "Could not add module %s - %s: %s\n",
                info,
                exc_info(sys)[1],
                exc_info(sys)[2]
            )
        end
    end
    if verbose && length(infos)
        println("Done.")
    end
    _SaveDicts()
end

function _Dump()
    println("Cache is in directory$(win32com_.__gen_path__)")
    d = OrderedDict()
    for (clsid, (typelibCLSID, lcid, major, minor)) in collect(clsidToTypelib)
        d[(typelibCLSID, lcid, major, minor)] = nothing
    end
    for (typelibCLSID, lcid, major, minor) in keys(d)
        mod = GetModuleForTypelib(typelibCLSID, lcid, major, minor)
        @printf("%s - %s\n", mod.__doc__, typelibCLSID)
    end
end

__init__()
function usage()
    usageString = "\t  Usage: gencache [-q] [-d] [-r]\n\n\t\t\t -q         - Quiet\n\t\t\t -d         - Dump the cache (typelibrary description and filename).\n\t\t\t -r         - Rebuild the cache dictionary from the existing .py files\n\t"
    println(usageString)
    quit(1)
end

if abspath(PROGRAM_FILE) == @__FILE__
    try
        opts, args = getopt(getopt, append!([PROGRAM_FILE], ARGS)[2:end], "qrd")
    catch exn
        let message = exn
            if message isa getopt.error
                println(message)
                usage()
            end
        end
    end
    if length(append!([PROGRAM_FILE], ARGS)) == 1 || args
        println(usage())
    end
    verbose = 1
    for (opt, val) in opts
        if opt == "-d"
            _Dump()
        end
        if opt == "-r"
            Rebuild(verbose)
        end
        if opt == "-q"
            verbose = 0
        end
    end
end
