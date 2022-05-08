using Printf
using PyCall
pythoncom = pyimport("pythoncom")
#= Generate a .py file from an OLE TypeLibrary file.


 This module is concerned only with the actual writing of
 a .py file.  It draws on the @build@ module, which builds
 the knowledge of a COM interface.

 =#
import win32ui
import pywin
using pywin.dialogs: status
import getopt
import codecs
usageHelp = " \nUsage:\n\n  makepy.py [-i] [-v|q] [-h] [-u] [-o output_file] [-d] [typelib, ...]\n\n  -i    -- Show information for the specified typelib.\n\n  -v    -- Verbose output.\n\n  -q    -- Quiet output.\n\n  -h    -- Do not generate hidden methods.\n\n  -u    -- Python 1.5 and earlier: Do NOT convert all Unicode objects to\n           strings.\n\n           Python 1.6 and later: Convert all Unicode objects to strings.\n\n  -o    -- Create output in a specified output file.  If the path leading\n           to the file does not exist, any missing directories will be\n           created.\n           NOTE: -o cannot be used with -d.  This will generate an error.\n\n  -d    -- Generate the base code now and the class code on demand.\n           Recommended for large type libraries.\n\n  typelib -- A TLB, DLL, OCX or anything containing COM type information.\n             If a typelib is not specified, a window containing a textbox\n             will open from which you can select a registered type\n             library.\n\nExamples:\n\n  makepy.py -d\n\n    Presents a list of registered type libraries from which you can make\n    a selection.\n\n  makepy.py -d \"Microsoft Excel 8.0 Object Library\"\n\n    Generate support for the type library with the specified description\n    (in this case, the MS Excel object model).\n\n"
import importlib
using win32com.client: genpy, selecttlb, gencache
using win32com.client: Dispatch
abstract type AbstractSimpleProgress <: Abstractgenpy.GeneratorProgress end
abstract type AbstractGUIProgress <: AbstractSimpleProgress end
bForDemandDefault = 0
error = "makepy.error"
function usage()
    write(sys.stderr, usageHelp)
    quit(2)
end

function ShowInfo(spec)
    if !(spec)
        tlbSpec = SelectTlb(selecttlb, selecttlb.FLAG_HIDDEN)
        if tlbSpec === nothing
            return
        end
        try
            tlb = LoadRegTypeLib(
                pythoncom,
                clsid(tlbSpec),
                major(tlbSpec),
                minor(tlbSpec),
                lcid(tlbSpec),
            )
        catch exn
            if exn isa com_error(pythoncom)
                write(
                    sys.stderr,
                    "Warning - could not load registered typelib \'%s\'\n" % clsid(tlbSpec),
                )
                tlb = nothing
            end
        end
        infos = [(tlb, tlbSpec)]
    else
        infos = GetTypeLibsForSpec(spec)
    end
    for (tlb, tlbSpec) in infos
        desc = desc(tlbSpec)
        if desc === nothing
            if tlb === nothing
                desc = "<Could not load typelib %s>" % dll(tlbSpec)
            else
                desc = GetDocumentation(tlb, -1)[1]
            end
        end
        println(desc)
        @printf(
            " %s, lcid=%s, major=%s, minor=%s",
            (clsid(tlbSpec), lcid(tlbSpec), major(tlbSpec), minor(tlbSpec))
        )
        println(" >>> # Use these commands in Python code to auto generate .py support")
        println(" >>> from win32com.client import gencache")
        @printf(
            " >>> gencache.EnsureModule(\'%s\', %s, %s, %s)",
            (clsid(tlbSpec), lcid(tlbSpec), major(tlbSpec), minor(tlbSpec))
        )
    end
end

mutable struct SimpleProgress <: AbstractSimpleProgress
    #= A simple progress class prints its output to stderr =#
    verboseLevel::Any
end
function Close(self::SimpleProgress)
    #= pass =#
end

function Finished(self::SimpleProgress)
    if self.verboseLevel > 1
        write(sys.stderr, "Generation complete..\n")
    end
end

function SetDescription(self::SimpleProgress, desc, maxticks = nothing)
    if self.verboseLevel
        write(sys.stderr, desc + "\n")
    end
end

function Tick(self::SimpleProgress, desc = nothing)
    #= pass =#
end

function VerboseProgress(self::SimpleProgress, desc, verboseLevel = 2)
    if self.verboseLevel >= verboseLevel
        write(sys.stderr, desc + "\n")
    end
end

function LogBeginGenerate(self::SimpleProgress, filename)
    VerboseProgress(self, "Generating to %s" % filename, 1)
end

function LogWarning(self::SimpleProgress, desc)
    VerboseProgress(self, "WARNING: " + desc, 1)
end

mutable struct GUIProgress <: AbstractGUIProgress
    dialog::Any

    GUIProgress(verboseLevel, dialog = nothing) = begin
        SimpleProgress.__init__(self, verboseLevel)
        new(verboseLevel, dialog)
    end
end
function Close(self::GUIProgress)
    if self.dialog != nothing
        Close(self.dialog)
        self.dialog = nothing
    end
end

function Starting(self::GUIProgress, tlb_desc)
    Starting(SimpleProgress, self, tlb_desc)
    if self.dialog === nothing
        self.dialog = ThreadedStatusProgressDialog(status, tlb_desc)
    else
        SetTitle(self.dialog, tlb_desc)
    end
end

function SetDescription(self::GUIProgress, desc, maxticks = nothing)
    SetText(self.dialog, desc)
    if maxticks
        SetMaxTicks(self.dialog, maxticks)
    end
end

function Tick(self::GUIProgress, desc = nothing)
    Tick(self.dialog)
    if desc != nothing
        SetText(self.dialog, desc)
    end
end

function GetTypeLibsForSpec(arg)::Vector
    #= Given an argument on the command line (either a file name, library
        description, or ProgID of an object) return a list of actual typelibs
        to use. =#
    typelibs = []
    try
        try
            tlb = LoadTypeLib(pythoncom, arg)
            spec = TypelibSpec(selecttlb, nothing, 0, 0, 0)
            FromTypelib(spec, tlb, arg)
            push!(typelibs, (tlb, spec))
        catch exn
            if exn isa com_error(pythoncom)
                tlbs = FindTlbsWithDescription(selecttlb, arg)
                if length(tlbs) == 0
                    try
                        ob = Dispatch(arg)
                        tlb, index = GetContainingTypeLib(GetTypeInfo(ob._oleobj_))
                        spec = TypelibSpec(selecttlb, nothing, 0, 0, 0)
                        FromTypelib(spec, tlb)
                        append(tlbs, spec)
                    catch exn
                        if exn isa com_error(pythoncom)
                            #= pass =#
                        end
                    end
                end
                if length(tlbs) == 0
                    @printf("Could not locate a type library matching \'%s\'", arg)
                end
                for spec in tlbs
                    if dll(spec) === nothing
                        tlb = LoadRegTypeLib(
                            pythoncom,
                            clsid(spec),
                            major(spec),
                            minor(spec),
                            lcid(spec),
                        )
                    else
                        tlb = LoadTypeLib(pythoncom, dll(spec))
                    end
                    attr = GetLibAttr(tlb)
                    major(spec) = attr[4]
                    minor(spec) = attr[5]
                    lcid(spec) = attr[2]
                    push!(typelibs, (tlb, spec))
                end
            end
        end
        return typelibs
    catch exn
        if exn isa com_error(pythoncom)
            t, v, tb = exc_info(sys)
            write(sys.stderr, "Unable to load type library from \'%s\' - %s\n" % (arg, v))
            tb = nothing
            quit(1)
        end
    end
end

function GenerateFromTypeLibSpec(
    typelibInfo,
    file = nothing,
    verboseLevel = nothing,
    progressInstance = nothing,
    bUnicodeToString = nothing,
    bForDemand = bForDemandDefault,
    bBuildHidden = 1,
)
    @assert(bUnicodeToString === nothing)
    if verboseLevel === nothing
        verboseLevel = 0
    end
    if bForDemand && file != nothing
        throw(
            RuntimeError(
                "You can only perform a demand-build when the output goes to the gen_py directory",
            ),
        )
    end
    if isa(typelibInfo, tuple)
        typelibCLSID, lcid, major, minor = typelibInfo
        tlb = LoadRegTypeLib(pythoncom, typelibCLSID, major, minor, lcid)
        spec = TypelibSpec(selecttlb, typelibCLSID, lcid, major, minor)
        FromTypelib(spec, tlb, string(typelibCLSID))
        typelibs = [(tlb, spec)]
    elseif isa(typelibInfo, selecttlb.TypelibSpec)
        if dll(typelibInfo) === nothing
            tlb = LoadRegTypeLib(
                pythoncom,
                clsid(typelibInfo),
                major(typelibInfo),
                minor(typelibInfo),
                lcid(typelibInfo),
            )
        else
            tlb = LoadTypeLib(pythoncom, dll(typelibInfo))
        end
        typelibs = [(tlb, typelibInfo)]
    elseif hasattr(typelibInfo, "GetLibAttr")
        tla = GetLibAttr(typelibInfo)
        guid = tla[1]
        lcid = tla[2]
        major = tla[4]
        minor = tla[5]
        spec = TypelibSpec(selecttlb, guid, lcid, major, minor)
        typelibs = [(typelibInfo, spec)]
    else
        typelibs = GetTypeLibsForSpec(typelibInfo)
    end
    if progressInstance === nothing
        progressInstance = SimpleProgress(verboseLevel)
    end
    progress = progressInstance
    bToGenDir = file === nothing
    for (typelib, info) in typelibs
        gen = Generator(genpy, typelib, dll(info), progress, bBuildHidden)
        if file === nothing
            this_name = GetGeneratedFileName(
                gencache,
                clsid(info),
                lcid(info),
                major(info),
                minor(info),
            )
            full_name = join
            if bForDemand
                try
                    std::fs::remove_file(full_name + ".py")
                catch exn
                    if exn isa os.error
                        #= pass =#
                    end
                end
                try
                    std::fs::remove_file(full_name + ".pyc")
                catch exn
                    if exn isa os.error
                        #= pass =#
                    end
                end
                try
                    std::fs::remove_file(full_name + ".pyo")
                catch exn
                    if exn isa os.error
                        #= pass =#
                    end
                end
                if !isdir(os.path, full_name)
                    mkdir(os, full_name)
                end
                outputName = join
            else
                outputName = full_name + ".py"
            end
            fileUse = open_writer(gen, outputName)
            LogBeginGenerate(progress, outputName)
        else
            fileUse = file
        end
        worked = false
        try
            generate(gen, fileUse, bForDemand)
            worked = true
        finally
            if file === nothing
                finish_writer(gen, outputName, fileUse, worked)
            end
        end
        invalidate_caches(importlib)
        if bToGenDir
            SetDescription(progress, "Importing module")
            AddModuleToCache(gencache, clsid(info), lcid(info), major(info), minor(info))
        end
    end
    Close(progress)
end

function GenerateChildFromTypeLibSpec(
    child,
    typelibInfo,
    verboseLevel = nothing,
    progressInstance = nothing,
    bUnicodeToString = nothing,
)
    @assert(bUnicodeToString === nothing)
    if verboseLevel === nothing
        verboseLevel = 0
    end
    if type_(typelibInfo) == type_(())
        typelibCLSID, lcid, major, minor = typelibInfo
        tlb = LoadRegTypeLib(pythoncom, typelibCLSID, major, minor, lcid)
    else
        tlb = typelibInfo
        tla = GetLibAttr(typelibInfo)
        typelibCLSID = tla[1]
        lcid = tla[2]
        major = tla[4]
        minor = tla[5]
    end
    spec = TypelibSpec(selecttlb, typelibCLSID, lcid, major, minor)
    FromTypelib(spec, tlb, string(typelibCLSID))
    typelibs = [(tlb, spec)]
    if progressInstance === nothing
        progressInstance = SimpleProgress(verboseLevel)
    end
    progress = progressInstance
    for (typelib, info) in typelibs
        dir_name = GetGeneratedFileName(
            gencache,
            clsid(info),
            lcid(info),
            major(info),
            minor(info),
        )
        dir_path_name = join
        LogBeginGenerate(progress, dir_path_name)
        gen = Generator(genpy, typelib, dll(info), progress)
        generate_child(gen, child, dir_path_name)
        SetDescription(progress, "Importing module")
        invalidate_caches(importlib)
        __import__(("win32com.gen_py." + dir_name) * "." + child)
    end
    Close(progress)
end

function main_func()::Int64
    hiddenSpec = 1
    outputName = nothing
    verboseLevel = 1
    doit = 1
    bForDemand = bForDemandDefault
    try
        opts, args = getopt(getopt, append!([PROGRAM_FILE], ARGS)[2:end], "vo:huiqd")
        for (o, v) in opts
            if o == "-h"
                hiddenSpec = 0
            elseif o == "-o"
                outputName = v
            elseif o == "-v"
                verboseLevel = verboseLevel + 1
            elseif o == "-q"
                verboseLevel = verboseLevel - 1
            elseif o == "-i"
                if length(args) == 0
                    ShowInfo(nothing)
                else
                    for arg in args
                        ShowInfo(arg)
                    end
                end
                doit = 0
            elseif o == "-d"
                bForDemand = !(bForDemand)
            end
        end
    catch exn
        let msg = exn
            if msg isa (error(getopt), error)
                write(sys.stderr, string(msg) * "\n")
                usage()
            end
        end
    end
    if bForDemand && outputName != nothing
        write(sys.stderr, "Can not use -d and -o together\n")
        usage()
    end
    if !(doit) != 0
        return 0
    end
    if length(args) == 0
        rc = SelectTlb(selecttlb)
        if rc === nothing
            quit(1)
        end
        args = [rc]
    end
    if outputName != nothing
        path = dirname(os.path, outputName)
        if path != "" && !exists(os.path, path)
            makedirs(os, path)
        end
        if version_info(sys) > (3, 0)
            f = readline(outputName)
        else
            f = readline(codecs)
        end
    else
        f = nothing
    end
    for arg in args
        GenerateFromTypeLibSpec(arg, f)
    end
    if f
        close(f)
    end
end

function main()
    rc = main_func()
    if rc != 0
        quit(rc)
    end
    quit(0)
end

main()
