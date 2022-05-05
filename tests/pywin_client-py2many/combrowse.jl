using Printf
#= A utility for browsing COM objects.

 Usage:

  Command Prompt

    Use the command *"python.exe catbrowse.py"*.  This will display
    display a fairly small, modal dialog.

  Pythonwin

    Use the "Run Script" menu item, and this will create the browser in an
    MDI window.  This window can be fully resized.

 Details

   This module allows browsing of registered Type Libraries, COM categories,
   and running COM objects.  The display is similar to the Pythonwin object
   browser, and displays the objects in a hierarchical window.

   Note that this module requires the win32ui (ie, Pythonwin) distribution to
   work.

 =#
abstract type AbstractHLIRoot <: Abstractbrowser.HLIPythonObject end
abstract type AbstractHLICOM <: Abstractbrowser.HLIPythonObject end
abstract type AbstractHLICLSID <: AbstractHLICOM end
abstract type AbstractHLI_Interface <: AbstractHLICOM end
abstract type AbstractHLI_Enum <: AbstractHLI_Interface end
abstract type AbstractHLI_IEnumMoniker <: AbstractHLI_Enum end
abstract type AbstractHLI_IMoniker <: AbstractHLI_Interface end
abstract type AbstractHLIHeadingCategory <: AbstractHLICOM end
abstract type AbstractHLICategory <: AbstractHLICOM end
abstract type AbstractHLIHelpFile <: AbstractHLICOM end
abstract type AbstractHLIRegisteredTypeLibrary <: AbstractHLICOM end
abstract type AbstractHLITypeLibEntry <: AbstractHLICOM end
abstract type AbstractHLICoClass <: AbstractHLITypeLibEntry end
abstract type AbstractHLITypeLibMethod <: AbstractHLITypeLibEntry end
abstract type AbstractHLITypeLibEnum <: AbstractHLITypeLibEntry end
abstract type AbstractHLITypeLibProperty <: AbstractHLICOM end
abstract type AbstractHLITypeLibFunction <: AbstractHLICOM end
abstract type AbstractHLITypeLib <: AbstractHLICOM end
abstract type AbstractHLIHeadingRegisterdTypeLibs <: AbstractHLICOM end
import win32con
import win32api
import win32ui

import pythoncom
using win32com.client: util
using pywin.tools: browser
mutable struct HLIRoot <: AbstractHLIRoot
    name::Any
end
function GetSubList(self::AbstractHLIRoot)
    return [
        HLIHeadingCategory(),
        HLI_IEnumMoniker(EnumRunning(GetRunningObjectTable(pythoncom)), "Running Objects"),
        HLIHeadingRegisterdTypeLibs(),
    ]
end

function __cmp__(self::AbstractHLIRoot, other)
    return cmp(self.name, name(other))
end

mutable struct HLICOM <: AbstractHLICOM
    name::Any
end
function GetText(self::AbstractHLICOM)
    return self.name
end

function CalculateIsExpandable(self::AbstractHLICOM)::Int64
    return 1
end

mutable struct HLICLSID <: AbstractHLICLSID
    name::Any

    HLICLSID(myobject, name = nothing) = begin
        if type_(myobject) == type_("")
            myobject = pythoncom.MakeIID(myobject)
        end
        if name === nothing
            try
                name = pythoncom.ProgIDFromCLSID(myobject)
            catch exn
                if exn isa pythoncom.com_error
                    name = string(myobject)
                end
            end
            name = "IID: " + name
        end
        HLICOM.__init__(self, myobject, name)
        new(myobject, name = nothing)
    end
end
function CalculateIsExpandable(self::AbstractHLICLSID)::Int64
    return 0
end

function GetSubList(self::AbstractHLICLSID)::Vector
    return []
end

mutable struct HLI_Interface <: AbstractHLI_Interface

end

mutable struct HLI_Enum <: AbstractHLI_Enum
    myobject::Any
end
function GetBitmapColumn(self::AbstractHLI_Enum)::Int64
    return 0
end

function CalculateIsExpandable(self::AbstractHLI_Enum)
    if self.myobject != nothing
        rc = length(Next(self.myobject, 1)) > 0
        Reset(self.myobject)
    else
        rc = 0
    end
    return rc
end

mutable struct HLI_IEnumMoniker <: AbstractHLI_IEnumMoniker
    myobject::Any
end
function GetSubList(self::AbstractHLI_IEnumMoniker)::Vector
    ctx = CreateBindCtx(pythoncom)
    ret = []
    for mon in Enumerator(util, self.myobject)
        push!(ret, HLI_IMoniker(mon, GetDisplayName(mon, ctx, nothing)))
    end
    return ret
end

mutable struct HLI_IMoniker <: AbstractHLI_IMoniker

end
function GetSubList(self::AbstractHLI_IMoniker)::Vector
    ret = []
    push!(ret, MakeHLI(browser, Hash(self.myobject), "Hash Value"))
    subenum = Enum(self.myobject, 1)
    push!(ret, HLI_IEnumMoniker(subenum, "Sub Monikers"))
    return ret
end

mutable struct HLIHeadingCategory <: AbstractHLIHeadingCategory

end
function GetText(self::AbstractHLIHeadingCategory)::String
    return "Registered Categories"
end

function GetSubList(self::AbstractHLIHeadingCategory)::Vector
    catinf = CoCreateInstance(
        pythoncom,
        pythoncom.CLSID_StdComponentCategoriesMgr,
        nothing,
        pythoncom.CLSCTX_INPROC,
        pythoncom.IID_ICatInformation,
    )
    enum = Enumerator(util, EnumCategories(catinf))
    ret = []
    try
        for (catid, lcid, desc) in enum
            push!(ret, HLICategory((catid, lcid, desc)))
        end
    catch exn
        if exn isa pythoncom.com_error
            #= pass =#
        end
    end
    return ret
end

mutable struct HLICategory <: AbstractHLICategory

end
function GetText(self::AbstractHLICategory)
    desc = self.myobject[3]
    if !(desc)
        desc = "(unnamed category)"
    end
    return desc
end

function GetSubList(self::AbstractHLICategory)::Vector
    DoWaitCursor(win32ui, 1)
    catid, lcid, desc = self.myobject
    catinf = CoCreateInstance(
        pythoncom,
        pythoncom.CLSID_StdComponentCategoriesMgr,
        nothing,
        pythoncom.CLSCTX_INPROC,
        pythoncom.IID_ICatInformation,
    )
    ret = []
    for clsid in Enumerator(util, EnumClassesOfCategories(catinf, (catid,), ()))
        push!(ret, HLICLSID(clsid))
    end
    DoWaitCursor(win32ui, 0)
    return ret
end

mutable struct HLIHelpFile <: AbstractHLIHelpFile

end
function CalculateIsExpandable(self::AbstractHLIHelpFile)::Int64
    return 0
end

function GetText(self::AbstractHLIHelpFile)::String

    fname, ctx = self.myobject
    base = split(os.path, fname)[2]
    return "Help reference in %s" % base
end

function TakeDefaultAction(self::AbstractHLIHelpFile)
    fname, ctx = self.myobject
    if ctx
        cmd = win32con.HELP_CONTEXT
    else
        cmd = win32con.HELP_FINDER
    end
    WinHelp(win32api, GetSafeHwnd(GetMainFrame(win32ui)), fname, cmd, ctx)
end

function GetBitmapColumn(self::AbstractHLIHelpFile)::Int64
    return 6
end

mutable struct HLIRegisteredTypeLibrary <: AbstractHLIRegisteredTypeLibrary

end
function GetSubList(self::AbstractHLIRegisteredTypeLibrary)::Vector

    clsidstr, versionStr = self.myobject
    collected = []
    helpPath = ""
    key = RegOpenKey(
        win32api,
        win32con.HKEY_CLASSES_ROOT,
        "TypeLib\\%s\\%s" % (clsidstr, versionStr),
    )
    DoWaitCursor(win32ui, 1)
    try
        num = 0
        while true
            try
                subKey = RegEnumKey(win32api, key, num)
            catch exn
                if exn isa win32api.error
                    break
                end
            end
            hSubKey = RegOpenKey(win32api, key, subKey)
            try
                value, typ = RegQueryValueEx(win32api, hSubKey, nothing)
                if typ == win32con.REG_EXPAND_SZ
                    value = ExpandEnvironmentStrings(win32api, value)
                end
            catch exn
                if exn isa win32api.error
                    value = ""
                end
            end
            if subKey == "HELPDIR"
                helpPath = value
            elseif subKey == "Flags"
                flags = value
            else
                try
                    lcid = parse(Int, subKey)
                    lcidkey = RegOpenKey(win32api, key, subKey)
                    lcidnum = 0
                    while true
                        try
                            platform = RegEnumKey(win32api, lcidkey, lcidnum)
                        catch exn
                            if exn isa win32api.error
                                break
                            end
                        end
                        try
                            hplatform = RegOpenKey(win32api, lcidkey, platform)
                            fname, typ = RegQueryValueEx(win32api, hplatform, nothing)
                            if typ == win32con.REG_EXPAND_SZ
                                fname = ExpandEnvironmentStrings(win32api, fname)
                            end
                        catch exn
                            if exn isa win32api.error
                                fname = ""
                            end
                        end
                        push!(collected, (lcid, platform, fname))
                        lcidnum = lcidnum + 1
                    end
                    RegCloseKey(win32api, lcidkey)
                catch exn
                    if exn isa ValueError
                        #= pass =#
                    end
                end
            end
            num = num + 1
        end
    finally
        DoWaitCursor(win32ui, 0)
        RegCloseKey(win32api, key)
    end
    ret = []
    push!(ret, HLICLSID(clsidstr))
    for (lcid, platform, fname) in collected
        extraDescs = []
        if platform != "win32"
            push!(extraDescs, platform)
        end
        if lcid
            push!(extraDescs, "locale=%s" % lcid)
        end
        extraDesc = ""
        if extraDescs
            extraDesc = " (%s)" % join(extraDescs, ", ")
        end
        push!(ret, HLITypeLib(fname, "Type Library" * extraDesc))
    end
    sort(ret)
    return ret
end

mutable struct HLITypeLibEntry <: AbstractHLITypeLibEntry

end
function GetText(self::AbstractHLITypeLibEntry)::String
    tlb, index = self.myobject
    name, doc, ctx, helpFile = GetDocumentation(tlb, index)
    try
        typedesc = HLITypeKinds[GetTypeInfoType(tlb, index)][2]
    catch exn
        if exn isa KeyError
            typedesc = "Unknown!"
        end
    end
    return (name + " - ") + typedesc
end

function GetSubList(self::AbstractHLITypeLibEntry)::Vector
    tlb, index = self.myobject
    name, doc, ctx, helpFile = GetDocumentation(tlb, index)
    ret = []
    if doc
        push!(ret, HLIDocString(browser, doc, "Doc"))
    end
    if helpFile
        push!(ret, HLIHelpFile((helpFile, ctx)))
    end
    return ret
end

mutable struct HLICoClass <: AbstractHLICoClass

end
function GetSubList(self::AbstractHLICoClass)
    ret = GetSubList(HLITypeLibEntry)
    tlb, index = self.myobject
    typeinfo = GetTypeInfo(tlb, index)
    attr = GetTypeAttr(typeinfo)
    for j = 0:attr[9]-1
        flags = GetImplTypeFlags(typeinfo, j)
        refType = GetRefTypeInfo(typeinfo, GetRefTypeOfImplType(typeinfo, j))
        refAttr = GetTypeAttr(refType)
        append(
            ret,
            MakeHLI(browser, refAttr[1], "Name=%s, Flags = %d" % (refAttr[1], flags)),
        )
    end
    return ret
end

mutable struct HLITypeLibMethod <: AbstractHLITypeLibMethod
    entry_type::String
    name::Any

    HLITypeLibMethod(ob, name = nothing) = begin
        HLITypeLibEntry.__init__(self, ob, name)
        new(ob, name = nothing)
    end
end
function GetSubList(self::AbstractHLITypeLibMethod)
    ret = GetSubList(HLITypeLibEntry)
    tlb, index = self.myobject
    typeinfo = GetTypeInfo(tlb, index)
    attr = GetTypeAttr(typeinfo)
    for i = 0:attr[8]-1
        append(ret, HLITypeLibProperty((typeinfo, i)))
    end
    for i = 0:attr[7]-1
        append(ret, HLITypeLibFunction((typeinfo, i)))
    end
    return ret
end

mutable struct HLITypeLibEnum <: AbstractHLITypeLibEnum
    name::Any
    id::Any
    typeinfo::Any

    HLITypeLibEnum(myitem) = begin
        HLITypeLibEntry.__init__(self, myitem, name)
        new(myitem)
    end
end
function GetText(self::AbstractHLITypeLibEnum)::String
    return self.name + " - Enum/Module"
end

function GetSubList(self::AbstractHLITypeLibEnum)::Vector
    ret = []
    typelib, index = self.myobject
    typeinfo = GetTypeInfo(typelib, index)
    attr = GetTypeAttr(typeinfo)
    for j = 0:attr[8]-1
        vdesc = GetVarDesc(typeinfo, j)
        name = GetNames(typeinfo, vdesc[1])[1]
        push!(ret, MakeHLI(browser, vdesc[2], name))
    end
    return ret
end

mutable struct HLITypeLibProperty <: AbstractHLITypeLibProperty
    id::Any
    name::Any

    HLITypeLibProperty(myitem) = begin
        HLICOM.__init__(self, myitem, name)
        new(myitem)
    end
end
function GetText(self::AbstractHLITypeLibProperty)::String
    return self.name + " - Property"
end

function GetSubList(self::AbstractHLITypeLibProperty)::Vector
    ret = []
    typeinfo, index = self.myobject
    names = GetNames(typeinfo, self.id)
    if length(names) > 1
        push!(ret, MakeHLI(browser, names[2:end], "Named Params"))
    end
    vd = GetVarDesc(typeinfo, index)
    push!(ret, MakeHLI(browser, self.id, "Dispatch ID"))
    push!(ret, MakeHLI(browser, vd[2], "Value"))
    push!(ret, MakeHLI(browser, vd[3], "Elem Desc"))
    push!(ret, MakeHLI(browser, vd[4], "Var Flags"))
    push!(ret, MakeHLI(browser, vd[5], "Var Kind"))
    return ret
end

mutable struct HLITypeLibFunction <: AbstractHLITypeLibFunction
    funcflags::Any
    id::Any
    name::Any
    type_flags::Any
    funckinds::Dict{Any,String}
    invokekinds::Dict{Any,String}
    vartypes::Dict{Any,String}

    HLITypeLibFunction(myitem) = begin
        HLICOM.__init__(self, myitem, name)
        new(myitem)
    end
end
function GetText(self::AbstractHLITypeLibFunction)::String
    return self.name + " - Function"
end

function MakeReturnTypeName(self::AbstractHLITypeLibFunction, typ)
    justtyp = typ & pythoncom.VT_TYPEMASK
    try
        typname = self.vartypes[justtyp+1]
    catch exn
        if exn isa KeyError
            typname = "?Bad type?"
        end
    end
    for (flag, desc) in self.type_flags
        if flag & typ
            typname = "%s(%s)" % (desc, typname)
        end
    end
    return typname
end

function MakeReturnType(self::AbstractHLITypeLibFunction, returnTypeDesc)
    if type_(returnTypeDesc) == type_(())
        first = returnTypeDesc[1]
        result = MakeReturnType(self, first)
        if first != pythoncom.VT_USERDEFINED
            result = result * " " + MakeReturnType(self, returnTypeDesc[2])
        end
        return result
    else
        return MakeReturnTypeName(self, returnTypeDesc)
    end
end

function GetSubList(self::AbstractHLITypeLibFunction)::Vector
    ret = []
    typeinfo, index = self.myobject
    names = GetNames(typeinfo, self.id)
    push!(ret, MakeHLI(browser, self.id, "Dispatch ID"))
    if length(names) > 1
        push!(ret, MakeHLI(browser, join(names[2:end], ", "), "Named Params"))
    end
    fd = GetFuncDesc(typeinfo, index)
    if fd[2]
        push!(ret, MakeHLI(browser, fd[2], "Possible result values"))
    end
    if fd[9]
        typ, flags, default = fd[9]
        val = MakeReturnType(self, typ)
        if flags
            val = "%s (Flags=%d, default=%s)" % (val, flags, default)
        end
        push!(ret, MakeHLI(browser, val, "Return Type"))
    end
    for argDesc in fd[3]
        typ, flags, default = argDesc
        val = MakeReturnType(self, typ)
        if flags
            val = "%s (Flags=%d)" % (val, flags)
        end
        if default != nothing
            val = "%s (Default=%s)" % (val, default)
        end
        push!(ret, MakeHLI(browser, val, "Argument"))
    end
    try
        fkind = self.funckinds[fd[4]+1]
    catch exn
        if exn isa KeyError
            fkind = "Unknown"
        end
    end
    push!(ret, MakeHLI(browser, fkind, "Function Kind"))
    try
        ikind = self.invokekinds[fd[5]+1]
    catch exn
        if exn isa KeyError
            ikind = "Unknown"
        end
    end
    push!(ret, MakeHLI(browser, ikind, "Invoke Kind"))
    push!(ret, MakeHLI(browser, fd[7], "Number Optional Params"))
    flagDescs = []
    for (flag, desc) in self.funcflags
        if flag & fd[10]
            push!(flagDescs, desc)
        end
    end
    if flagDescs
        push!(ret, MakeHLI(browser, join(flagDescs, ", "), "Function Flags"))
    end
    return ret
end

HLITypeKinds = Dict(
    pythoncom.TKIND_ENUM => (HLITypeLibEnum, "Enumeration"),
    pythoncom.TKIND_RECORD => (HLITypeLibEntry, "Record"),
    pythoncom.TKIND_MODULE => (HLITypeLibEnum, "Module"),
    pythoncom.TKIND_INTERFACE => (HLITypeLibMethod, "Interface"),
    pythoncom.TKIND_DISPATCH => (HLITypeLibMethod, "Dispatch"),
    pythoncom.TKIND_COCLASS => (HLICoClass, "CoClass"),
    pythoncom.TKIND_ALIAS => (HLITypeLibEntry, "Alias"),
    pythoncom.TKIND_UNION => (HLITypeLibEntry, "Union"),
)
mutable struct HLITypeLib <: AbstractHLITypeLib
    myobject::Any
end
function GetSubList(self::AbstractHLITypeLib)::Vector
    ret = []
    push!(ret, MakeHLI(browser, self.myobject, "Filename"))
    try
        tlb = LoadTypeLib(pythoncom, self.myobject)
    catch exn
        if exn isa pythoncom.com_error
            return [MakeHLI(browser, "%s can not be loaded" % self.myobject)]
        end
    end
    for i = 0:GetTypeInfoCount(tlb)-1
        try
            push!(ret, HLITypeKinds[GetTypeInfoType(tlb, i)][1]((tlb, i)))
        catch exn
            if exn isa pythoncom.com_error
                push!(ret, MakeHLI(browser, "The type info can not be loaded!"))
            end
        end
    end
    sort(ret)
    return ret
end

mutable struct HLIHeadingRegisterdTypeLibs <: AbstractHLIHeadingRegisterdTypeLibs

end
function GetText(self::AbstractHLIHeadingRegisterdTypeLibs)::String
    return "Registered Type Libraries"
end

function GetSubList(self::AbstractHLIHeadingRegisterdTypeLibs)::Vector
    ret = []
    key = RegOpenKey(win32api, win32con.HKEY_CLASSES_ROOT, "TypeLib")
    DoWaitCursor(win32ui, 1)
    try
        num = 0
        while true
            try
                keyName = RegEnumKey(win32api, key, num)
            catch exn
                if exn isa win32api.error
                    break
                end
            end
            subKey = RegOpenKey(win32api, key, keyName)
            name = nothing
            try
                subNum = 0
                bestVersion = 0.0
                while true
                    try
                        versionStr = RegEnumKey(win32api, subKey, subNum)
                    catch exn
                        if exn isa win32api.error
                            break
                        end
                    end
                    try
                        versionFlt = float(versionStr)
                    catch exn
                        if exn isa ValueError
                            versionFlt = 0
                        end
                    end
                    if versionFlt > bestVersion
                        bestVersion = versionFlt
                        name = RegQueryValue(win32api, subKey, versionStr)
                    end
                    subNum = subNum + 1
                end
            finally
                RegCloseKey(win32api, subKey)
            end
            if name != nothing
                push!(ret, HLIRegisteredTypeLibrary((keyName, versionStr), name))
            end
            num = num + 1
        end
    finally
        RegCloseKey(win32api, key)
        DoWaitCursor(win32ui, 0)
    end
    sort(ret)
    return ret
end

function main_func(modal = false)
    using pywin.tools: hierlist
    root = HLIRoot("COM Browser")
    if "app" in modules(sys)
        MakeTemplate(browser)
        OpenObject(browser.template, root)
    else
        dlg = dynamic_browser(browser, root)
        if modal
            DoModal(dlg)
        else
            CreateWindow(dlg)
            ShowWindow(dlg)
        end
    end
end

function main()
    main_func()
    ni = _GetInterfaceCount(pythoncom)
    ng = _GetGatewayCount(pythoncom)
    if ni || ng
        @printf("Warning - exiting with %d/%d objects alive", (ni, ng))
    end
end

main()
