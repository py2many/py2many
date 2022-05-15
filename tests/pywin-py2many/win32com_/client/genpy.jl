module genpy
#= genpy.py - The worker for makepy.  See makepy.py for more details

This code was moved simply to speed Python in normal circumstances.  As the makepy.py
is normally run from the command line, it reparses the code each time.  Now makepy
is nothing more than the command line handler and public interface.

The makepy command line etc handling is also getting large enough in its own right!
 =#
using PyCall
pythoncom = pyimport("pythoncom")

include("../__init__.jl")
# import win32com_

include("build.jl")
abstract type AbstractWritableItem end
abstract type AbstractRecordItem <: Abstractbuild.OleItem end
abstract type AbstractAliasItem <: Abstractbuild.OleItem end
abstract type AbstractEnumerationItem <: Abstractbuild.OleItem end
abstract type AbstractVTableItem <: Abstractbuild.VTableItem end
abstract type AbstractDispatchItem <: Abstractbuild.DispatchItem end
abstract type AbstractCoClassItem <: Abstractbuild.OleItem end
abstract type AbstractGeneratorProgress end
abstract type AbstractGenerator end
error = "makepy.error"
makepy_version = "0.5.01"
GEN_FULL = "full"
GEN_DEMAND_BASE = "demand(base)"
GEN_DEMAND_CHILD = "demand(child)"
mapVTToTypeString = Dict(
    pythoncom.VT_I2 => "types.IntType",
    pythoncom.VT_I4 => "types.IntType",
    pythoncom.VT_R4 => "types.FloatType",
    pythoncom.VT_R8 => "types.FloatType",
    pythoncom.VT_BSTR => "types.StringType",
    pythoncom.VT_BOOL => "types.IntType",
    pythoncom.VT_VARIANT => "types.TypeType",
    pythoncom.VT_I1 => "types.IntType",
    pythoncom.VT_UI1 => "types.IntType",
    pythoncom.VT_UI2 => "types.IntType",
    pythoncom.VT_UI4 => "types.IntType",
    pythoncom.VT_I8 => "types.LongType",
    pythoncom.VT_UI8 => "types.LongType",
    pythoncom.VT_INT => "types.IntType",
    pythoncom.VT_DATE => "pythoncom.PyTimeType",
    pythoncom.VT_UINT => "types.IntType",
)
function MakeDefaultArgsForPropertyPut(argsDesc)::Tuple
    ret = []
    for desc in argsDesc[2:end]
        default = MakeDefaultArgRepr(build, desc)
        if default === nothing
            break
        end
        push!(ret, default)
    end
    return tuple(ret)
end

function MakeMapLineEntry(dispid, wFlags, retType, argTypes, user, resultCLSID)
    argTypes = tuple([what[begin:2] for what in argTypes])
    return "(%s, %d, %s, %s, \"%s\", %s)" %
           (dispid, wFlags, retType[begin:2], argTypes, user, resultCLSID)
end

function MakeEventMethodName(eventName)::String
    if eventName[begin:2] == "On"
        return eventName
    else
        return "On" + eventName
    end
end

function WriteSinkEventMap(obj, stream)
    write(stream)
    for (name, entry) in append!(
        append!(collect(items(obj.propMapGet)), collect(items(obj.propMapPut))),
        collect(items(obj.mapFuncs)),
    )
        fdesc = entry.desc
        write(
            stream,
            "\t\t%9d : \"%s\",",
            (fdesc.memid, MakeEventMethodName(entry.names[1])),
        )
    end
    write(stream)
end

mutable struct WritableItem <: AbstractWritableItem
    doc
    order
end
function __cmp__(self::WritableItem, other)
    #= Compare for sorting =#
    ret = cmp(self.order, other.order)
    if ret == 0 && self.doc
        ret = cmp(self.doc[1], other.doc[1])
    end
    return ret
end

function __lt__(self::WritableItem, other)::Bool
    if self.order == other.order
        return self.doc < other.doc
    end
    return self.order < other.order
end

function __repr__(self::WritableItem)
    return "OleItem: doc=%s, order=%d" % (repr(self.doc), self.order)
end

mutable struct RecordItem <: build.OleItem
    clsid
    bForUser::Int64
    doc
    order::Int64
    typename::String

    RecordItem(
        typeInfo,
        typeAttr,
        doc = nothing,
        bForUser = 1,
        order::Int64 = 9,
        typename::String = "RECORD",
    ) = begin
        build.OleItem.__init__(self, doc)
        new(typeInfo, typeAttr, doc, bForUser, order, typename)
    end
end
function WriteClass(self::RecordItem, generator)
    #= pass =#
end

function WriteAliasesForItem(item, aliasItems, stream)
    for alias in values(aliasItems)
        if item.doc && alias.aliasDoc && alias.aliasDoc[1] == item.doc[1]
            WriteAliasItem(alias, aliasItems, stream)
        end
    end
end

mutable struct AliasItem <: build.OleItem
    aliasAttr
    aliasDoc
    attr
    bWritten::Int64
    bForUser::Int64
    doc
    order::Int64
    typename::String

    AliasItem(
        typeinfo,
        attr,
        doc = nothing,
        bForUser = 1,
        order::Int64 = 2,
        typename::String = "ALIAS",
    ) = begin
        build.OleItem.__init__(self, doc)
        if type_(ai) == type_(()) && type_(ai[1]) == type_(0)
            href = ai[1]
            alinfo = typeinfo.GetRefTypeInfo(href)
            aliasDoc = alinfo.GetDocumentation(-1)
            aliasAttr = alinfo.GetTypeAttr()
        else
            aliasDoc = nothing
            aliasAttr = nothing
        end
        new(typeinfo, attr, doc, bForUser, order, typename)
    end
end
function WriteAliasItem(self::AliasItem, aliasDict, stream)
    if self.bWritten
        return
    end
    if self.aliasDoc
        depName = self.aliasDoc[1]
        if depName in aliasDict
            WriteAliasItem(aliasDict[depName+1], aliasDict, stream)
        end
        write(stream)
    else
        ai = self.attr[15]
        if type_(ai) == type_(0)
            try
                typeStr = mapVTToTypeString[ai]
                write(stream, "# %s=%s", (self.doc[1], typeStr))
            catch exn
                if exn isa KeyError
                    write(stream)
                end
            end
        end
    end
    println(file = stream)
    self.bWritten = 1
end

mutable struct EnumerationItem <: build.OleItem
    clsid
    hidden
    mapVars::Dict
    bForUser::Int64
    doc
    order::Int64
    typename::String

    EnumerationItem(
        typeinfo,
        attr,
        doc = nothing,
        bForUser = 1,
        order::Int64 = 1,
        typename::String = "ENUMERATION",
    ) = begin
        build.OleItem.__init__(self, doc)
        for j = 0:attr[7]
            vdesc = typeinfo.GetVarDesc(j)
            name = typeinfo.GetNames(vdesc[0])[0]
            mapVars[name] = build.MapEntry(vdesc)
        end
        new(typeinfo, attr, doc, bForUser, order, typename)
    end
end
function WriteEnumerationItems(self::EnumerationItem, stream)::Int64
    num = 0
    enumName = self.doc[1]
    names = collect(keys(self.mapVars))
    sort(names)
    for name in names
        entry = self.mapVars[name]
        vdesc = entry.desc
        if vdesc[5] == pythoncom.VAR_CONST
            val = vdesc[2]
            use = repr(val)
            try
                compile(use, "<makepy>", "eval")
            catch exn
                if exn isa SyntaxError
                    use = replace(use, "\"", "\'")
                    use =
                        ("\"" + use) *
                        "\"" *
                        " # This VARIANT type cannot be converted automatically"
                end
            end
            write(
                stream,
                "\t%-30s=%-10s # from enum %s",
                (MakePublicAttributeName(build, name, true), use, enumName),
            )
            num += 1
        end
    end
    return num
end

mutable struct VTableItem <: build.VTableItem
    bIsDispatch
    bWritten::Int64
    python_name
    vtableFuncs
    order::Int64

    VTableItem(bIsDispatch, bWritten::Int64, python_name, vtableFuncs, order::Int64 = 4) =
        new(bIsDispatch, bWritten, python_name, vtableFuncs, order)
end
function WriteClass(self::VTableItem, generator)
    WriteVTableMap(self, generator)
    self.bWritten = 1
end

function WriteVTableMap(self::VTableItem, generator)
    stream = generator.file
    write(stream, "%s_vtables_dispatch_ = %d", (self.python_name, self.bIsDispatch))
    write(stream, "%s_vtables_ = [", (self.python_name,))
    for v in self.vtableFuncs
        names, dispid, desc = v
        @assert(desc.desckind == pythoncom.DESCKIND_FUNCDESC)
        arg_reprs = []
        item_num = 0
        write(stream)
        for name in names
            write(stream)
            item_num = item_num + 1
            if (item_num % 5) == 0
                write(stream)
            end
        end
        write(stream, "), %d, (%r, %r, [", (dispid, desc.memid, desc.scodeArray))
        for arg in desc.args
            item_num = item_num + 1
            if (item_num % 5) == 0
                write(stream)
            end
            defval = MakeDefaultArgRepr(build, arg)
            if arg[4] === nothing
                arg3_repr = nothing
            else
                arg3_repr = repr(arg[4])
            end
            write(stream)
        end
        write(stream)
        write(stream)
        write(stream)
        write(stream)
        write(stream)
        write(stream)
        write(stream)
        write(stream)
        write(stream)
    end
    write(stream)
    println(file = stream)
end

mutable struct DispatchItem <: build.DispatchItem
    bIsDispatch
    bIsSink
    bWritten::Int64
    clsid
    coclass_clsid
    mapFuncs
    python_name
    type_attr
    doc
    order::Int64

    DispatchItem(typeinfo, attr, doc = nothing, order::Int64 = 3) = begin
        build.DispatchItem.__init__(self, typeinfo, attr, doc)
        new(typeinfo, attr, doc, order)
    end
end
function WriteClass(self::DispatchItem, generator)
    if !(self.bIsDispatch) && !(self.type_attr.typekind == pythoncom.TKIND_DISPATCH)
        return
    end
    if self.bIsSink
        WriteEventSinkClassHeader(self, generator)
        WriteCallbackClassBody(self, generator)
    else
        WriteClassHeader(self, generator)
        WriteClassBody(self, generator)
    end
    println(file = generator.file)
    self.bWritten = 1
end

function WriteClassHeader(self::DispatchItem, generator)
    checkWriteDispatchBaseClass(generator)
    doc = self.doc
    stream = generator.file
    write(stream)
    if doc[2]
        write(stream)
    end
    try
        progId = ProgIDFromCLSID(pythoncom, self.clsid)
        write(stream, "\t# This class is creatable by the name \'%s\'", progId)
    catch exn
        if exn isa pythoncom.com_error
            #= pass =#
        end
    end
    write(stream)
    if self.coclass_clsid === nothing
        write(stream)
    else
        write(stream)
    end
    println(file = stream)
    self.bWritten = 1
end

function WriteEventSinkClassHeader(self::DispatchItem, generator)
    checkWriteEventBaseClass(generator)
    doc = self.doc
    stream = generator.file
    write(stream)
    if doc[2]
        write(stream)
    end
    try
        progId = ProgIDFromCLSID(pythoncom, self.clsid)
        write(stream, "\t# This class is creatable by the name \'%s\'", progId)
    catch exn
        if exn isa pythoncom.com_error
            #= pass =#
        end
    end
    write(stream)
    if self.coclass_clsid === nothing
        write(stream)
    else
        write(stream)
    end
    write(stream)
    WriteSinkEventMap(self, stream)
    println(file = stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    write(stream)
    println(file = stream)
    self.bWritten = 1
end

function WriteCallbackClassBody(self::DispatchItem, generator)
    stream = generator.file
    write(stream)
    write(stream)
    for (name, entry) in append!(
        append!(collect(items(self.propMapGet)), collect(items(self.propMapPut))),
        collect(items(self.mapFuncs)),
    )
        fdesc = entry.desc
        methName = MakeEventMethodName(entry.names[1])
        write(stream)
        if entry.doc && entry.doc[2]
            write(stream)
        end
    end
    println(file = stream)
    self.bWritten = 1
end

function WriteClassBody(self::DispatchItem, generator)
    stream = generator.file
    names = collect(keys(self.mapFuncs))
    sort(names)
    specialItems = Dict(
        "count" => nothing,
        "item" => nothing,
        "value" => nothing,
        "_newenum" => nothing,
    )
    itemCount = nothing
    for name in names
        entry = self.mapFuncs[name+1]
        @assert(entry.desc.desckind == pythoncom.DESCKIND_FUNCDESC)
        dispid = entry.desc.memid
        if entry.desc.wFuncFlags & pythoncom.FUNCFLAG_FRESTRICTED &&
           dispid != pythoncom.DISPID_NEWENUM
            continue
        end
        if entry.desc.funckind != pythoncom.FUNC_DISPATCH
            continue
        end
        if dispid == pythoncom.DISPID_VALUE
            lkey = "value"
        elseif dispid == pythoncom.DISPID_NEWENUM
            specialItems["_newenum"] = (entry, entry.desc.invkind, nothing)
            continue
        else
            lkey = lower(name)
        end
        if lkey in keys(specialItems) && specialItems[lkey] === nothing
            specialItems[lkey] = (entry, entry.desc.invkind, nothing)
        end
        if generator.bBuildHidden || !(entry.hidden)
            if GetResultName(entry)
                write(stream)
            end
            if entry.wasProperty
                write(
                    stream,
                    "\t# The method %s is actually a property, but must be used as a method to correctly pass the arguments",
                    name,
                )
            end
            ret = MakeFuncMethod(self, entry, MakePublicAttributeName(build, name))
            for line in ret
                write(stream)
            end
        end
    end
    write(stream)
    names = collect(keys(self.propMap))
    sort(names)
    for key in names
        entry = self.propMap[key+1]
        if generator.bBuildHidden || !(entry.hidden)
            resultName = GetResultName(entry)
            if resultName
                write(
                    stream,
                    "\t\t# Property \'%s\' is an object of type \'%s\'",
                    (key, resultName),
                )
            end
            lkey = lower(key)
            details = entry.desc
            resultDesc = details[3]
            argDesc = ()
            mapEntry = MakeMapLineEntry(
                details.memid,
                pythoncom.DISPATCH_PROPERTYGET,
                resultDesc,
                argDesc,
                key,
                GetResultCLSIDStr(entry),
            )
            if details.memid == pythoncom.DISPID_VALUE
                lkey = "value"
            elseif details.memid == pythoncom.DISPID_NEWENUM
                lkey = "_newenum"
            else
                lkey = lower(key)
            end
            if lkey in keys(specialItems) && specialItems[lkey] === nothing
                specialItems[lkey] = (entry, pythoncom.DISPATCH_PROPERTYGET, mapEntry)
                if details.memid == pythoncom.DISPID_NEWENUM
                    continue
                end
            end
            write(
                stream,
                "\t\t\"%s\": %s,",
                (MakePublicAttributeName(build, key), mapEntry),
            )
        end
    end
    names = collect(keys(self.propMapGet))
    sort(names)
    for key in names
        entry = self.propMapGet[key+1]
        if generator.bBuildHidden || !(entry.hidden)
            if GetResultName(entry)
                write(
                    stream,
                    "\t\t# Method \'%s\' returns object of type \'%s\'",
                    (key, GetResultName(entry)),
                )
            end
            details = entry.desc
            @assert(details.desckind == pythoncom.DESCKIND_FUNCDESC)
            lkey = lower(key)
            argDesc = details[3]
            resultDesc = details[9]
            mapEntry = MakeMapLineEntry(
                details[1],
                pythoncom.DISPATCH_PROPERTYGET,
                resultDesc,
                argDesc,
                key,
                GetResultCLSIDStr(entry),
            )
            if details.memid == pythoncom.DISPID_VALUE
                lkey = "value"
            elseif details.memid == pythoncom.DISPID_NEWENUM
                lkey = "_newenum"
            else
                lkey = lower(key)
            end
            if lkey in keys(specialItems) && specialItems[lkey] === nothing
                specialItems[lkey] = (entry, pythoncom.DISPATCH_PROPERTYGET, mapEntry)
                if details.memid == pythoncom.DISPID_NEWENUM
                    continue
                end
            end
            write(
                stream,
                "\t\t\"%s\": %s,",
                (MakePublicAttributeName(build, key), mapEntry),
            )
        end
    end
    write(stream)
    write(stream)
    names = collect(keys(self.propMap))
    sort(names)
    for key in names
        entry = self.propMap[key+1]
        if generator.bBuildHidden || !(entry.hidden)
            lkey = lower(key)
            details = entry.desc
            defArgDesc = MakeDefaultArgRepr(build, details[3])
            if defArgDesc === nothing
                defArgDesc = ""
            else
                defArgDesc = defArgDesc * ","
            end
            write(
                stream,
                "\t\t\"%s\" : ((%s, LCID, %d, 0),(%s)),",
                (
                    MakePublicAttributeName(build, key),
                    details[1],
                    pythoncom.DISPATCH_PROPERTYPUT,
                    defArgDesc,
                ),
            )
        end
    end
    names = collect(keys(self.propMapPut))
    sort(names)
    for key in names
        entry = self.propMapPut[key+1]
        if generator.bBuildHidden || !(entry.hidden)
            details = entry.desc
            defArgDesc = MakeDefaultArgsForPropertyPut(details[3])
            write(
                stream,
                "\t\t\"%s\": ((%s, LCID, %d, 0),%s),",
                (MakePublicAttributeName(build, key), details[1], details[5], defArgDesc),
            )
        end
    end
    write(stream)
    if specialItems["value"]
        entry, invoketype, propArgs = specialItems["value"]
        if propArgs === nothing
            typename = "method"
            ret = MakeFuncMethod(self, entry, "__call__")
        else
            typename = "property"
            ret = ["\tdef __call__(self):\n\t\treturn self._ApplyTypes_(*%s)" % propArgs]
        end
        write(stream, "\t# Default %s for this class is \'%s\'", (typename, entry.names[1]))
        for line in ret
            write(stream)
        end
        write(stream)
        write(stream)
        write(stream)
        write(stream)
    end
    if specialItems["_newenum"]
        enumEntry, invoketype, propArgs = specialItems["_newenum"]
        @assert(enumEntry.desc.desckind == pythoncom.DESCKIND_FUNCDESC)
        invkind = enumEntry.desc.invkind
        resultCLSID = GetResultCLSIDStr(enumEntry)
    else
        invkind = pythoncom.DISPATCH_METHOD | pythoncom.DISPATCH_PROPERTYGET
        resultCLSID = "None"
    end
    if resultCLSID == "None" && "Item" in self.mapFuncs
        resultCLSID = GetResultCLSIDStr(self.mapFuncs["Item"])
    end
    write(stream)
    write(stream)
    write(stream)
    write(
        stream,
        "\t\t\tob = self._oleobj_.InvokeTypes(%d,LCID,%d,(13, 10),())",
        (pythoncom.DISPID_NEWENUM, invkind),
    )
    write(stream)
    write(stream)
    write(stream, "\t\treturn win32com_.client.util.Iterator(ob, %s)", resultCLSID)
    if specialItems["item"]
        entry, invoketype, propArgs = specialItems["item"]
        resultCLSID = GetResultCLSIDStr(entry)
        write(stream)
        write(stream)
        write(stream)
        write(stream)
        write(
            stream,
            "\t\treturn self._get_good_object_(self._oleobj_.Invoke(*(%d, LCID, %d, 1, key)), \"Item\", %s)",
            (entry.desc.memid, invoketype, resultCLSID),
        )
    end
    if specialItems["count"]
        entry, invoketype, propArgs = specialItems["count"]
        if propArgs === nothing
            typename = "method"
            ret = MakeFuncMethod(self, entry, "__len__")
        else
            typename = "property"
            ret = ["\tdef __len__(self):\n\t\treturn self._ApplyTypes_(*%s)" % propArgs]
        end
        write(
            stream,
            "\t#This class has Count() %s - allow len(ob) to provide this",
            typename,
        )
        for line in ret
            write(stream)
        end
        write(stream)
        write(stream)
        write(stream)
    end
end

mutable struct CoClassItem <: build.OleItem
    bIsDispatch::Int64
    bWritten::Int64
    clsid
    interfaces
    python_name
    sources
    bForUser::Int64
    doc
    order::Int64
    typename::String

    CoClassItem(
        typeinfo,
        attr,
        doc = nothing,
        sources = [],
        interfaces = [],
        bForUser = 1,
        order::Int64 = 5,
        typename::String = "COCLASS",
    ) = begin
        build.OleItem.__init__(self, doc)
        new(typeinfo, attr, doc, sources, interfaces, bForUser, order, typename)
    end
end
function WriteClass(self::CoClassItem, generator)
    checkWriteCoClassBaseClass(generator)
    doc = self.doc
    stream = generator.file
    if generator.generate_type == GEN_DEMAND_CHILD
        referenced_items = []
        for (ref, flag) in self.sources
            push!(referenced_items, ref)
        end
        for (ref, flag) in self.interfaces
            push!(referenced_items, ref)
        end
        write(stream)
        for ref in referenced_items
            write(
                stream,
                "__import__(\'%s.%s\')",
                (generator.base_mod_name, ref.python_name),
            )
            write(
                stream,
                "%s = sys.modules[\'%s.%s\'].%s",
                (
                    ref.python_name,
                    generator.base_mod_name,
                    ref.python_name,
                    ref.python_name,
                ),
            )
            ref.bWritten = 1
        end
    end
    try
        progId = ProgIDFromCLSID(pythoncom, self.clsid)
        write(stream, "# This CoClass is known by the name \'%s\'", progId)
    catch exn
        if exn isa pythoncom.com_error
            #= pass =#
        end
    end
    write(stream, "class %s(CoClassBaseClass): # A CoClass", self.python_name)
    if doc && doc[2]
        write(stream)
    end
    write(stream, "\tCLSID = %r", (self.clsid,))
    write(stream)
    defItem = nothing
    for (item, flag) in self.sources
        if flag & pythoncom.IMPLTYPEFLAG_FDEFAULT
            defItem = item
        end
        if item.bWritten
            key = item.python_name
        else
            key = repr(string(item.clsid))
        end
        write(stream, "\t\t%s,", key)
    end
    write(stream)
    if defItem
        if defItem.bWritten
            defName = defItem.python_name
        else
            defName = repr(string(defItem.clsid))
        end
        write(stream, "\tdefault_source = %s", (defName,))
    end
    write(stream)
    defItem = nothing
    for (item, flag) in self.interfaces
        if flag & pythoncom.IMPLTYPEFLAG_FDEFAULT
            defItem = item
        end
        if item.bWritten
            key = item.python_name
        else
            key = repr(string(item.clsid))
        end
        write(stream, "\t\t%s,", (key,))
    end
    write(stream)
    if defItem
        if defItem.bWritten
            defName = defItem.python_name
        else
            defName = repr(string(defItem.clsid))
        end
        write(stream, "\tdefault_interface = %s", (defName,))
    end
    self.bWritten = 1
    println(file = stream)
end

mutable struct GeneratorProgress <: AbstractGeneratorProgress
    tlb_desc

    GeneratorProgress() = begin
        #= pass =#
        new()
    end
end
function Starting(self::GeneratorProgress, tlb_desc)
    #= Called when the process starts. =#
    self.tlb_desc = tlb_desc
end

function Finished(self::GeneratorProgress)
    #= Called when the process is complete. =#
end

function SetDescription(self::GeneratorProgress, desc, maxticks = nothing)
    #= We are entering a major step.  If maxticks, then this
            is how many ticks we expect to make until finished
             =#
end

function Tick(self::GeneratorProgress, desc = nothing)
    #= Minor progress step.  Can provide new description if necessary =#
end

function VerboseProgress(self::GeneratorProgress, desc)
    #= Verbose/Debugging output. =#
end

function LogWarning(self::GeneratorProgress, desc)
    #= If a warning is generated =#
end

function LogBeginGenerate(self::GeneratorProgress, filename)
    #= pass =#
end

function Close(self::GeneratorProgress)
    #= pass =#
end

mutable struct Generator <: AbstractGenerator
    bBuildHidden
    bHaveWrittenCoClassBaseClass::Int64
    bHaveWrittenDispatchBaseClass::Int64
    bHaveWrittenEventBaseClass::Int64
    base_mod_name
    file
    generate_type::String
    progress
    sourceFilename
    typelib
    bUnicodeToString

    Generator(
        typelib,
        sourceFilename,
        progressObject,
        bBuildHidden = 1,
        bUnicodeToString = nothing,
    ) = begin
        @assert(bUnicodeToString === nothing)
        new(typelib, sourceFilename, progressObject, bBuildHidden, bUnicodeToString)
    end
end
function CollectOleItemInfosFromType(self::Generator)::Vector
    ret = []
    for i = 0:GetTypeInfoCount(self.typelib)-1
        info = GetTypeInfo(self.typelib, i)
        infotype = GetTypeInfoType(self.typelib, i)
        doc = GetDocumentation(self.typelib, i)
        attr = GetTypeAttr(info)
        push!(ret, (info, infotype, doc, attr))
    end
    return ret
end

function _Build_CoClass(self::Generator, type_info_tuple)::Tuple
    info, infotype, doc, attr = type_info_tuple
    child_infos = []
    for j = 0:attr[9]-1
        flags = GetImplTypeFlags(info, j)
        try
            refType = GetRefTypeInfo(info, GetRefTypeOfImplType(info, j))
        catch exn
            if exn isa pythoncom.com_error
                continue
            end
        end
        refAttr = GetTypeAttr(refType)
        push!(
            child_infos,
            (
                info,
                refAttr.typekind,
                refType,
                GetDocumentation(refType, -1),
                refAttr,
                flags,
            ),
        )
    end
    newItem = CoClassItem(info, attr, doc)
    return (newItem, child_infos)
end

function _Build_CoClassChildren(
    self::Generator,
    coclass,
    coclass_info,
    oleItems,
    vtableItems,
)
    sources = Dict()
    interfaces = Dict()
    for (info, info_type, refType, doc, refAttr, flags) in coclass_info
        if refAttr.typekind == pythoncom.TKIND_DISPATCH ||
           refAttr.typekind == pythoncom.TKIND_INTERFACE &&
           refAttr[12] & pythoncom.TYPEFLAG_FDISPATCHABLE
            clsid = refAttr[1]
            if clsid in oleItems
                dispItem = oleItems[clsid+1]
            else
                dispItem = DispatchItem(refType, refAttr, doc)
                oleItems[dispItem.clsid+1] = dispItem
            end
            dispItem.coclass_clsid = coclass.clsid
            if flags & pythoncom.IMPLTYPEFLAG_FSOURCE
                dispItem.bIsSink = 1
                sources[dispItem.clsid] = (dispItem, flags)
            else
                interfaces[dispItem.clsid] = (dispItem, flags)
            end
            if clsid ∉ vtableItems && refAttr[12] & pythoncom.TYPEFLAG_FDUAL
                refType = GetRefTypeInfo(refType, GetRefTypeOfImplType(refType, -1))
                refAttr = GetTypeAttr(refType)
                @assert(refAttr.typekind == pythoncom.TKIND_INTERFACE)
                vtableItem = VTableItem(refType, refAttr, doc)
                vtableItems[clsid+1] = vtableItem
            end
        end
    end
    coclass.sources = collect(values(sources))
    coclass.interfaces = collect(values(interfaces))
end

function _Build_Interface(self::Generator, type_info_tuple)::Tuple
    info, infotype, doc, attr = type_info_tuple
    oleItem = nothing
    vtableItem = nothing
    if infotype == pythoncom.TKIND_DISPATCH ||
       infotype == pythoncom.TKIND_INTERFACE && attr[12] & pythoncom.TYPEFLAG_FDISPATCHABLE
        oleItem = DispatchItem(info, attr, doc)
        if attr.wTypeFlags & pythoncom.TYPEFLAG_FDUAL
            refhtype = GetRefTypeOfImplType(info, -1)
            info = GetRefTypeInfo(info, refhtype)
            attr = GetTypeAttr(info)
            infotype = pythoncom.TKIND_INTERFACE
        else
            infotype = nothing
        end
    end
    @assert(infotype in [nothing, pythoncom.TKIND_INTERFACE])
    if infotype == pythoncom.TKIND_INTERFACE
        vtableItem = VTableItem(info, attr, doc)
    end
    return (oleItem, vtableItem)
end

function BuildOleItemsFromType(self::Generator)::Tuple
    @assert(self.bBuildHidden)
    oleItems = Dict()
    enumItems = Dict()
    recordItems = Dict()
    vtableItems = Dict()
    for type_info_tuple in CollectOleItemInfosFromType(self)
        info, infotype, doc, attr = type_info_tuple
        clsid = attr[1]
        if infotype == pythoncom.TKIND_ENUM || infotype == pythoncom.TKIND_MODULE
            newItem = EnumerationItem(info, attr, doc)
            enumItems[newItem.doc[1]] = newItem
        elseif infotype in [pythoncom.TKIND_DISPATCH, pythoncom.TKIND_INTERFACE]
            if clsid ∉ oleItems
                oleItem, vtableItem = _Build_Interface(self, type_info_tuple)
                oleItems[clsid] = oleItem
                if vtableItem != nothing
                    vtableItems[clsid] = vtableItem
                end
            end
        elseif infotype == pythoncom.TKIND_RECORD || infotype == pythoncom.TKIND_UNION
            newItem = RecordItem(info, attr, doc)
            recordItems[newItem.clsid] = newItem
        elseif infotype == pythoncom.TKIND_ALIAS
            continue
        elseif infotype == pythoncom.TKIND_COCLASS
            newItem, child_infos = _Build_CoClass(self, type_info_tuple)
            _Build_CoClassChildren(self, newItem, child_infos, oleItems, vtableItems)
            oleItems[newItem.clsid] = newItem
        else
            LogWarning(self.progress, "Unknown TKIND found: %d" % infotype)
        end
    end
    return (oleItems, enumItems, recordItems, vtableItems)
end

function open_writer(self::Generator, filename, encoding = "mbcs")
    temp_filename = get_temp_filename(self, filename)
    return readline(temp_filename)
end

function finish_writer(self::Generator, filename, f, worked)
    close(f)
    try
        std::fs::remove_file(filename)
    catch exn
        if exn isa os.error
            #= pass =#
        end
    end
    temp_filename = get_temp_filename(self, filename)
    if worked
        try
            rename(os, temp_filename, filename)
        catch exn
            if exn isa os.error
                try
                    std::fs::remove_file(filename)
                catch exn
                    if exn isa os.error
                        #= pass =#
                    end
                end
                rename(os, temp_filename, filename)
            end
        end
    else
        std::fs::remove_file(temp_filename)
    end
end

function get_temp_filename(self::Generator, filename)
    return "%s.%d.temp" % (filename, getpid(os))
end

function generate(self::Generator, file, is_for_demand = 0)
    if is_for_demand
        self.generate_type = GEN_DEMAND_BASE
    else
        self.generate_type = GEN_FULL
    end
    self.file = file
    do_generate(self)
    self.file = nothing
    Finished(self.progress)
end

function do_gen_file_header(self::Generator)
    la = GetLibAttr(self.typelib)
    moduleDoc = GetDocumentation(self.typelib, -1)
    docDesc = ""
    if moduleDoc[2]
        docDesc = moduleDoc[2]
    end
    self.bHaveWrittenDispatchBaseClass = 0
    self.bHaveWrittenCoClassBaseClass = 0
    self.bHaveWrittenEventBaseClass = 0
    @assert(self.file.encoding)
    encoding = self.file.encoding
    write(self.file, "# -*- coding: %s -*-", (encoding,))
    write(self.file, "# Created by makepy.py version %s", (makepy_version,))
    write(self.file, "# By python version %s", (replace(sys.version, "\n", "-"),))
    if self.sourceFilename
        write(
            self.file,
            "# From type library \'%s\'",
            (split(os.path, self.sourceFilename)[2],),
        )
    end
    write(self.file, "# On %s", ctime(time, pylib::time()))
    write(self.file)
    write(self.file)
    write(self.file, "python_version = 0x%x", (sys.hexversion,))
    println(file = self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    println(file = self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    println(file = self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    println(file = self.file)
end

function do_generate(self::Generator)
    moduleDoc = GetDocumentation(self.typelib, -1)
    stream = self.file
    docDesc = ""
    if moduleDoc[2]
        docDesc = moduleDoc[2]
    end
    Starting(self.progress, docDesc)
    SetDescription(self.progress, "Building definitions from type library...")
    do_gen_file_header(self)
    oleItems, enumItems, recordItems, vtableItems = BuildOleItemsFromType(self)
    SetDescription(
        self.progress,
        "Generating...",
        (length(oleItems) + length(enumItems)) + length(vtableItems),
    )
    if enumItems
        write(stream)
        items = collect(values(enumItems))
        sort(items)
        num_written = 0
        for oleitem in items
            num_written += WriteEnumerationItems(oleitem, stream)
            Tick(self.progress)
        end
        if !(num_written) != 0
            write(stream)
        end
        println(file = stream)
    end
    if self.generate_type == GEN_FULL
        items = [l for l in values(oleItems) if l != nothing]
        sort(items)
        for oleitem in items
            Tick(self.progress)
            WriteClass(oleitem, self)
        end
        items = collect(values(vtableItems))
        sort(items)
        for oleitem in items
            Tick(self.progress)
            WriteClass(oleitem, self)
        end
    else
        Tick(self.progress, length(oleItems) + length(vtableItems))
    end
    write(stream)
    for record in values(recordItems)
        if record.clsid == pythoncom.IID_NULL
            write(
                stream,
                "\t###%s: %s, # Record disabled because it doesn\'t have a non-null GUID",
                (repr(record.doc[1]), repr(string(record.clsid))),
            )
        else
            write(stream, "\t%s: %s,", (repr(record.doc[1]), repr(string(record.clsid))))
        end
    end
    write(stream)
    println(file = stream)
    if self.generate_type == GEN_FULL
        write(stream)
        for item in values(oleItems)
            if item != nothing && item.bWritten
                write(stream, "\t\'%s\' : %s,", (string(item.clsid), item.python_name))
            end
        end
        write(stream)
        write(stream)
        write(stream)
        write(stream)
        write(stream)
        for item in values(vtableItems)
            write(stream, "\t\'%s\' : \'%s\',", (item.clsid, item.python_name))
        end
        write(stream)
        println(file = stream)
    else
        write(stream)
        write(stream)
        for item in values(oleItems)
            if item != nothing
                write(
                    stream,
                    "\t\'%s\' : %s,",
                    (string(item.clsid), repr(item.python_name)),
                )
            end
        end
        write(stream)
        write(stream)
        write(stream)
        for item in values(vtableItems)
            write(stream, "\t\'%s\' : \'%s\',", (item.clsid, item.python_name))
        end
        write(stream)
        println(file = stream)
    end
    println(file = stream)
    map = Dict()
    for item in values(oleItems)
        if item != nothing && !isa(item, CoClassItem)
            map[item.python_name] = item.clsid
        end
    end
    for item in values(vtableItems)
        map[item.python_name] = item.clsid
    end
    write(stream)
    for (name, iid) in items(map)
        write(stream, "\t\'%s\' : \'%s\',", (name, iid))
    end
    write(stream)
    println(file = stream)
    if enumItems
        write(stream)
    end
    println(file = stream)
end

function generate_child(self::Generator, child, dir)
    #= Generate a single child.  May force a few children to be built as we generate deps =#
    self.generate_type = GEN_DEMAND_CHILD
    la = GetLibAttr(self.typelib)
    lcid = la[2]
    clsid = la[1]
    major = la[4]
    minor = la[5]
    self.base_mod_name =
        ("win32com_.gen_py." + string(clsid)[2:-1]) + ("x%sx%sx%s" % (lcid, major, minor))
    try
        oleItems = Dict()
        vtableItems = Dict()
        infos = CollectOleItemInfosFromType(self)
        found = 0
        for type_info_tuple in infos
            info, infotype, doc, attr = type_info_tuple
            if infotype == pythoncom.TKIND_COCLASS
                coClassItem, child_infos = _Build_CoClass(self, type_info_tuple)
                found = MakePublicAttributeName(build, doc[1]) == child
                if !(found)
                    for (info, info_type, refType, doc, refAttr, flags) in child_infos
                        if MakePublicAttributeName(build, doc[1]) == child
                            found = 1
                            break
                        end
                    end
                end
                if found
                    oleItems[coClassItem.clsid] = coClassItem
                    _Build_CoClassChildren(
                        self,
                        coClassItem,
                        child_infos,
                        oleItems,
                        vtableItems,
                    )
                    break
                end
            end
        end
        if !(found) != 0
            for type_info_tuple in infos
                info, infotype, doc, attr = type_info_tuple
                if infotype in [pythoncom.TKIND_INTERFACE, pythoncom.TKIND_DISPATCH]
                    if MakePublicAttributeName(build, doc[1]) == child
                        found = 1
                        oleItem, vtableItem = _Build_Interface(self, type_info_tuple)
                        oleItems[clsid] = oleItem
                        if vtableItem != nothing
                            vtableItems[clsid] = vtableItem
                        end
                    end
                end
            end
        end
        @assert(found)
        items = Dict()
        for (key, value) in items(oleItems)
            items[key] = (value, nothing)
        end
        for (key, value) in items(vtableItems)
            existing = get(items, key, nothing)
            if existing != nothing
                new_val = (existing[1], value)
            else
                new_val = (nothing, value)
            end
            items[key] = new_val
        end
        SetDescription(self.progress, "Generating...", length(items))
        for (oleitem, vtableitem) in values(items)
            an_item = oleitem || vtableitem
            @assert(!(self.file))
            out_name = join + ".py"
            worked = false
            self.file = open_writer(self, out_name)
            try
                if oleitem != nothing
                    do_gen_child_item(self, oleitem)
                end
                if vtableitem != nothing
                    do_gen_child_item(self, vtableitem)
                end
                Tick(self.progress)
                worked = true
            finally
                finish_writer(self, out_name, self.file, worked)
                self.file = nothing
            end
        end
    finally
        Finished(self.progress)
    end
end

function do_gen_child_item(self::Generator, oleitem)
    moduleDoc = GetDocumentation(self.typelib, -1)
    docDesc = ""
    if moduleDoc[2]
        docDesc = moduleDoc[2]
    end
    Starting(self.progress, docDesc)
    SetDescription(self.progress, "Building definitions from type library...")
    do_gen_file_header(self)
    WriteClass(oleitem, self)
    if oleitem.bWritten
        write(
            self.file,
            "win32com_.client.CLSIDToClass.RegisterCLSID( \"%s\", %s )",
            (oleitem.clsid, oleitem.python_name),
        )
    end
end

function checkWriteDispatchBaseClass(self::Generator)
    if !(self.bHaveWrittenDispatchBaseClass) != 0
        write(self.file)
        self.bHaveWrittenDispatchBaseClass = 1
    end
end

function checkWriteCoClassBaseClass(self::Generator)
    if !(self.bHaveWrittenCoClassBaseClass) != 0
        write(self.file)
        self.bHaveWrittenCoClassBaseClass = 1
    end
end

function checkWriteEventBaseClass(self::Generator)
    if !(self.bHaveWrittenEventBaseClass) != 0
        self.bHaveWrittenEventBaseClass = 1
    end
end

function main()
    println("This is a worker module.  Please use makepy to generate Python files.")
end

main()
end
