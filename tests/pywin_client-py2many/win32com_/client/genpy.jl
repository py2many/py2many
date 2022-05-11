module genpy
#= genpy.py - The worker for makepy.  See makepy.py for more details

This code was moved simply to speed Python in normal circumstances.  As the makepy.py
is normally run from the command line, it reparses the code each time.  Now makepy
is nothing more than the command line handler and public interface.

The makepy command line etc handling is also getting large enough in its own right!
 =#
using PyCall
pythoncom = pyimport("pythoncom")



import win32com_

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
    VT_I2(pythoncom) => "types.IntType",
    VT_I4(pythoncom) => "types.IntType",
    VT_R4(pythoncom) => "types.FloatType",
    VT_R8(pythoncom) => "types.FloatType",
    VT_BSTR(pythoncom) => "types.StringType",
    VT_BOOL(pythoncom) => "types.IntType",
    VT_VARIANT(pythoncom) => "types.TypeType",
    VT_I1(pythoncom) => "types.IntType",
    VT_UI1(pythoncom) => "types.IntType",
    VT_UI2(pythoncom) => "types.IntType",
    VT_UI4(pythoncom) => "types.IntType",
    VT_I8(pythoncom) => "types.LongType",
    VT_UI8(pythoncom) => "types.LongType",
    VT_INT(pythoncom) => "types.IntType",
    VT_DATE(pythoncom) => "pythoncom.PyTimeType",
    VT_UINT(pythoncom) => "types.IntType",
)
function MakeDefaultArgsForPropertyPut(argsDesc)::Tuple
    ret = []
    for desc in argsDesc[2:end]
        default = __init__(build.MakeDefaultArgRepr, desc)
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
        fdesc = desc(entry)
        write(
            stream,
            "\t\t%9d : \"%s\",",
            (memid(fdesc), MakeEventMethodName(names(entry)[1])),
        )
    end
    write(stream)
end

mutable struct WritableItem <: AbstractWritableItem
    doc::Any
    order::Any
end
function __cmp__(self::WritableItem, other)
    #= Compare for sorting =#
    ret = cmp(self.order, order(other))
    if ret == 0 && self.doc
        ret = cmp(self.doc[1], doc(other)[1])
    end
    return ret
end

function __lt__(self::WritableItem, other)::Bool
    if self.order == order(other)
        return self.doc < doc(other)
    end
    return self.order < order(other)
end

function __repr__(self::WritableItem)
    return "OleItem: doc=%s, order=%d" % (repr(self.doc), self.order)
end

mutable struct RecordItem <: build.OleItem.__init__
    bForUser::Int64
    clsid::Any
    doc::Any
    order::Int64
    typename::String

    RecordItem(
        typeInfo,
        typeAttr,
        doc = nothing,
        bForUser = 1,
        clsid = typeAttr[1],
        order::Int64 = 9,
        typename::String = "RECORD",
    ) = begin
        build.OleItem.__init__(self, doc)
        new(typeInfo, typeAttr, doc, bForUser, clsid, order, typename)
    end
end
function WriteClass(self::RecordItem, generator)
    #= pass =#
end

function WriteAliasesForItem(item, aliasItems, stream)
    for alias in values(aliasItems)
        if doc(item) && aliasDoc(alias) && aliasDoc(alias)[1] == doc(item)[1]
            WriteAliasItem(alias, aliasItems, stream)
        end
    end
end

mutable struct AliasItem <: build.OleItem.__init__
    aliasDoc::Any
    attr::Any
    bWritten::Any
    ai::Any
    bForUser::Int64
    doc::Any
    order::Int64
    typename::String

    AliasItem(
        typeinfo,
        attr,
        doc = nothing,
        bForUser = 1,
        ai = attr[15],
        order::Int64 = 2,
        typename::String = "ALIAS",
    ) = begin
        build.OleItem.__init__(self, doc)
        if type_(ai) == type_(()) && type_(ai[1]) == type_(0)
            href = ai[1]
            alinfo = typeinfo.GetRefTypeInfo(href)
            self.aliasDoc = alinfo.GetDocumentation(-1)
            self.aliasAttr = alinfo.GetTypeAttr()
        else
            self.aliasDoc = nothing
            self.aliasAttr = nothing
        end
        new(typeinfo, attr, doc, bForUser, ai, order, typename)
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
    println(stream)
    self.bWritten = 1
end

mutable struct EnumerationItem <: build.OleItem.__init__
    bForUser::Int64
    clsid::Any
    doc::Any
    hidden::Any
    mapVars::Dict
    order::Int64
    typeFlags::Any
    typename::String

    EnumerationItem(
        typeinfo,
        attr,
        doc = nothing,
        bForUser = 1,
        clsid = attr[1],
        hidden = typeFlags & TYPEFLAG_FHIDDEN(pythoncom) ||
                 typeFlags & TYPEFLAG_FRESTRICTED(pythoncom),
        mapVars::Dict = Dict(),
        order::Int64 = 1,
        typeFlags = attr[12],
        typename::String = "ENUMERATION",
    ) = begin
        build.OleItem.__init__(self, doc)
        for j = 0:attr[7]
            vdesc = typeinfo.GetVarDesc(j)
            name = typeinfo.GetNames(vdesc[0])[0]
            self.mapVars[name] = build.MapEntry(vdesc)
        end
        new(
            typeinfo,
            attr,
            doc,
            bForUser,
            clsid,
            hidden,
            mapVars,
            order,
            typeFlags,
            typename,
        )
    end
end
function WriteEnumerationItems(self::EnumerationItem, stream)::Int64
    num = 0
    enumName = self.doc[1]
    names = collect(keys(self.mapVars))
    sort(names)
    for name in names
        entry = self.mapVars[name+1]
        vdesc = desc(entry)
        if vdesc[5] == VAR_CONST(pythoncom)
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
                (__init__(build.MakePublicAttributeName, name, true), use, enumName),
            )
            num += 1
        end
    end
    return num
end

mutable struct VTableItem <: build.VTableItem.__init__
    bIsDispatch::Any
    bWritten::Any
    python_name::Any
    vtableFuncs::Any
    order::Int64

    VTableItem(
        bIsDispatch::Any,
        bWritten::Any,
        python_name::Any,
        vtableFuncs::Any,
        order::Int64 = 4,
    ) = new(bIsDispatch, bWritten, python_name, vtableFuncs, order)
end
function WriteClass(self::VTableItem, generator)
    WriteVTableMap(self, generator)
    self.bWritten = 1
end

function WriteVTableMap(self::VTableItem, generator)
    stream = file(generator)
    write(stream, "%s_vtables_dispatch_ = %d", (self.python_name, self.bIsDispatch))
    write(stream, "%s_vtables_ = [", (self.python_name,))
    for v in self.vtableFuncs
        names, dispid, desc = v
        @assert(desckind(desc) == DESCKIND_FUNCDESC(pythoncom))
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
        write(stream, "), %d, (%r, %r, [", (dispid, memid(desc), scodeArray(desc)))
        for arg in args(desc)
            item_num = item_num + 1
            if (item_num % 5) == 0
                write(stream)
            end
            defval = __init__(build.MakeDefaultArgRepr, arg)
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
    println(stream)
end

mutable struct DispatchItem <: build.DispatchItem.__init__
    bIsDispatch::Any
    bIsSink::Any
    bWritten::Any
    clsid::Any
    mapFuncs::Any
    python_name::Any
    coclass_clsid::Any
    doc::Any
    order::Int64
    type_attr::Any

    DispatchItem(
        typeinfo,
        attr,
        doc = nothing,
        coclass_clsid = nothing,
        order::Int64 = 3,
        type_attr = attr,
    ) = begin
        build.DispatchItem.__init__(self, typeinfo, attr, doc)
        new(typeinfo, attr, doc, coclass_clsid, order, type_attr)
    end
end
function WriteClass(self::DispatchItem, generator)
    if !(self.bIsDispatch) && !(self.type_attr.typekind == TKIND_DISPATCH(pythoncom))
        return
    end
    if self.bIsSink
        WriteEventSinkClassHeader(self, generator)
        WriteCallbackClassBody(self, generator)
    else
        WriteClassHeader(self, generator)
        WriteClassBody(self, generator)
    end
    println(file(generator))
    self.bWritten = 1
end

function WriteClassHeader(self::DispatchItem, generator)
    checkWriteDispatchBaseClass(generator)
    doc = self.doc
    stream = file(generator)
    write(stream)
    if doc[2]
        write(stream)
    end
    try
        progId = ProgIDFromCLSID(pythoncom, self.clsid)
        write(stream, "\t# This class is creatable by the name \'%s\'", progId)
    catch exn
        if exn isa com_error(pythoncom)
            #= pass =#
        end
    end
    write(stream)
    if self.coclass_clsid === nothing
        write(stream)
    else
        write(stream)
    end
    println(stream)
    self.bWritten = 1
end

function WriteEventSinkClassHeader(self::DispatchItem, generator)
    checkWriteEventBaseClass(generator)
    doc = self.doc
    stream = file(generator)
    write(stream)
    if doc[2]
        write(stream)
    end
    try
        progId = ProgIDFromCLSID(pythoncom, self.clsid)
        write(stream, "\t# This class is creatable by the name \'%s\'", progId)
    catch exn
        if exn isa com_error(pythoncom)
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
    println(stream)
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
    println(stream)
    self.bWritten = 1
end

function WriteCallbackClassBody(self::DispatchItem, generator)
    stream = file(generator)
    write(stream)
    write(stream)
    for (name, entry) in append!(
        append!(collect(items(self.propMapGet)), collect(items(self.propMapPut))),
        collect(items(self.mapFuncs)),
    )
        fdesc = desc(entry)
        methName = MakeEventMethodName(names(entry)[1])
        write(stream)
        if doc(entry) && doc(entry)[2]
            write(stream)
        end
    end
    println(stream)
    self.bWritten = 1
end

function WriteClassBody(self::DispatchItem, generator)
    stream = file(generator)
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
        @assert(desckind(entry.desc) == DESCKIND_FUNCDESC(pythoncom))
        dispid = memid(entry.desc)
        if wFuncFlags(entry.desc) & FUNCFLAG_FRESTRICTED(pythoncom) &&
           dispid != DISPID_NEWENUM(pythoncom)
            continue
        end
        if funckind(entry.desc) != FUNC_DISPATCH(pythoncom)
            continue
        end
        if dispid == DISPID_VALUE(pythoncom)
            lkey = "value"
        elseif dispid == DISPID_NEWENUM(pythoncom)
            specialItems["_newenum"] = (entry, invkind(entry.desc), nothing)
            continue
        else
            lkey = lower(name)
        end
        if lkey in keys(specialItems) && specialItems[lkey] === nothing
            specialItems[lkey] = (entry, invkind(entry.desc), nothing)
        end
        if bBuildHidden(generator) || !hidden(entry)
            if GetResultName(entry)
                write(stream)
            end
            if wasProperty(entry)
                write(
                    stream,
                    "\t# The method %s is actually a property, but must be used as a method to correctly pass the arguments",
                    name,
                )
            end
            ret = MakeFuncMethod(self, entry, __init__(build.MakePublicAttributeName, name))
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
        if bBuildHidden(generator) || !hidden(entry)
            resultName = GetResultName(entry)
            if resultName
                write(
                    stream,
                    "\t\t# Property \'%s\' is an object of type \'%s\'",
                    (key, resultName),
                )
            end
            lkey = lower(key)
            details = desc(entry)
            resultDesc = details[3]
            argDesc = ()
            mapEntry = MakeMapLineEntry(
                memid(details),
                DISPATCH_PROPERTYGET(pythoncom),
                resultDesc,
                argDesc,
                key,
                GetResultCLSIDStr(entry),
            )
            if memid(details) == DISPID_VALUE(pythoncom)
                lkey = "value"
            elseif memid(details) == DISPID_NEWENUM(pythoncom)
                lkey = "_newenum"
            else
                lkey = lower(key)
            end
            if lkey in keys(specialItems) && specialItems[lkey] === nothing
                specialItems[lkey] = (entry, DISPATCH_PROPERTYGET(pythoncom), mapEntry)
                if memid(details) == DISPID_NEWENUM(pythoncom)
                    continue
                end
            end
            write(
                stream,
                "\t\t\"%s\": %s,",
                (__init__(build.MakePublicAttributeName, key), mapEntry),
            )
        end
    end
    names = collect(keys(self.propMapGet))
    sort(names)
    for key in names
        entry = self.propMapGet[key+1]
        if bBuildHidden(generator) || !hidden(entry)
            if GetResultName(entry)
                write(
                    stream,
                    "\t\t# Method \'%s\' returns object of type \'%s\'",
                    (key, GetResultName(entry)),
                )
            end
            details = desc(entry)
            @assert(desckind(details) == DESCKIND_FUNCDESC(pythoncom))
            lkey = lower(key)
            argDesc = details[3]
            resultDesc = details[9]
            mapEntry = MakeMapLineEntry(
                details[1],
                DISPATCH_PROPERTYGET(pythoncom),
                resultDesc,
                argDesc,
                key,
                GetResultCLSIDStr(entry),
            )
            if memid(details) == DISPID_VALUE(pythoncom)
                lkey = "value"
            elseif memid(details) == DISPID_NEWENUM(pythoncom)
                lkey = "_newenum"
            else
                lkey = lower(key)
            end
            if lkey in keys(specialItems) && specialItems[lkey] === nothing
                specialItems[lkey] = (entry, DISPATCH_PROPERTYGET(pythoncom), mapEntry)
                if memid(details) == DISPID_NEWENUM(pythoncom)
                    continue
                end
            end
            write(
                stream,
                "\t\t\"%s\": %s,",
                (__init__(build.MakePublicAttributeName, key), mapEntry),
            )
        end
    end
    write(stream)
    write(stream)
    names = collect(keys(self.propMap))
    sort(names)
    for key in names
        entry = self.propMap[key+1]
        if bBuildHidden(generator) || !hidden(entry)
            lkey = lower(key)
            details = desc(entry)
            defArgDesc = __init__(build.MakeDefaultArgRepr, details[3])
            if defArgDesc === nothing
                defArgDesc = ""
            else
                defArgDesc = defArgDesc * ","
            end
            write(
                stream,
                "\t\t\"%s\" : ((%s, LCID, %d, 0),(%s)),",
                (
                    __init__(build.MakePublicAttributeName, key),
                    details[1],
                    DISPATCH_PROPERTYPUT(pythoncom),
                    defArgDesc,
                ),
            )
        end
    end
    names = collect(keys(self.propMapPut))
    sort(names)
    for key in names
        entry = self.propMapPut[key+1]
        if bBuildHidden(generator) || !hidden(entry)
            details = desc(entry)
            defArgDesc = MakeDefaultArgsForPropertyPut(details[3])
            write(
                stream,
                "\t\t\"%s\": ((%s, LCID, %d, 0),%s),",
                (
                    __init__(build.MakePublicAttributeName, key),
                    details[1],
                    details[5],
                    defArgDesc,
                ),
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
        write(
            stream,
            "\t# Default %s for this class is \'%s\'",
            (typename, names(entry)[1]),
        )
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
        @assert(desckind(enumEntry.desc) == DESCKIND_FUNCDESC(pythoncom))
        invkind = invkind(enumEntry.desc)
        resultCLSID = GetResultCLSIDStr(enumEntry)
    else
        invkind = DISPATCH_METHOD(pythoncom) | DISPATCH_PROPERTYGET(pythoncom)
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
        (DISPID_NEWENUM(pythoncom), invkind),
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
            (memid(desc(entry)), invoketype, resultCLSID),
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

mutable struct CoClassItem <: build.OleItem.__init__
    bWritten::Any
    interfaces::Any
    python_name::Any
    sources::Any
    bForUser::Int64
    bIsDispatch::Int64
    clsid::Any
    doc::Any
    order::Int64
    typename::String

    CoClassItem(
        typeinfo,
        attr,
        doc = nothing,
        sources = [],
        interfaces = [],
        bForUser = 1,
        bIsDispatch::Int64 = 1,
        clsid = attr[1],
        order::Int64 = 5,
        typename::String = "COCLASS",
    ) = begin
        build.OleItem.__init__(self, doc)
        new(
            typeinfo,
            attr,
            doc,
            sources,
            interfaces,
            bForUser,
            bIsDispatch,
            clsid,
            order,
            typename,
        )
    end
end
function WriteClass(self::CoClassItem, generator)
    checkWriteCoClassBaseClass(generator)
    doc = self.doc
    stream = file(generator)
    if generate_type(generator) == GEN_DEMAND_CHILD
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
                (base_mod_name(generator), python_name(ref)),
            )
            write(
                stream,
                "%s = sys.modules[\'%s.%s\'].%s",
                (
                    python_name(ref),
                    base_mod_name(generator),
                    python_name(ref),
                    python_name(ref),
                ),
            )
            bWritten(ref) = 1
        end
    end
    try
        progId = ProgIDFromCLSID(pythoncom, self.clsid)
        write(stream, "# This CoClass is known by the name \'%s\'", progId)
    catch exn
        if exn isa com_error(pythoncom)
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
        if flag & IMPLTYPEFLAG_FDEFAULT(pythoncom)
            defItem = item
        end
        if bWritten(item)
            key = python_name(item)
        else
            key = repr(string(clsid(item)))
        end
        write(stream, "\t\t%s,", key)
    end
    write(stream)
    if defItem
        if bWritten(defItem)
            defName = python_name(defItem)
        else
            defName = repr(string(clsid(defItem)))
        end
        write(stream, "\tdefault_source = %s", (defName,))
    end
    write(stream)
    defItem = nothing
    for (item, flag) in self.interfaces
        if flag & IMPLTYPEFLAG_FDEFAULT(pythoncom)
            defItem = item
        end
        if bWritten(item)
            key = python_name(item)
        else
            key = repr(string(clsid(item)))
        end
        write(stream, "\t\t%s,", (key,))
    end
    write(stream)
    if defItem
        if bWritten(defItem)
            defName = python_name(defItem)
        else
            defName = repr(string(clsid(defItem)))
        end
        write(stream, "\tdefault_interface = %s", (defName,))
    end
    self.bWritten = 1
    println(stream)
end

mutable struct GeneratorProgress <: AbstractGeneratorProgress
    tlb_desc::Any

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
    bBuildHidden::Any
    base_mod_name::Any
    generate_type::Any
    sourceFilename::Any
    typelib::Any
    bHaveWrittenCoClassBaseClass::Int64
    bHaveWrittenDispatchBaseClass::Int64
    bHaveWrittenEventBaseClass::Int64
    bUnicodeToString::Any
    file::Any
    progress::Any

    Generator(
        typelib,
        sourceFilename,
        progressObject,
        bBuildHidden = 1,
        bUnicodeToString = nothing,
        bHaveWrittenCoClassBaseClass::Int64 = 0,
        bHaveWrittenDispatchBaseClass::Int64 = 0,
        bHaveWrittenEventBaseClass::Int64 = 0,
        file = nothing,
        progress = progressObject,
    ) = begin
        @assert(bUnicodeToString === nothing)
        new(
            typelib,
            sourceFilename,
            progressObject,
            bBuildHidden,
            bUnicodeToString,
            bHaveWrittenCoClassBaseClass,
            bHaveWrittenDispatchBaseClass,
            bHaveWrittenEventBaseClass,
            file,
            progress,
        )
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
            if exn isa com_error(pythoncom)
                continue
            end
        end
        refAttr = GetTypeAttr(refType)
        push!(
            child_infos,
            (
                info,
                typekind(refAttr),
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
        if typekind(refAttr) == TKIND_DISPATCH(pythoncom) ||
           typekind(refAttr) == TKIND_INTERFACE(pythoncom) &&
           refAttr[12] & TYPEFLAG_FDISPATCHABLE(pythoncom)
            clsid = refAttr[1]
            if clsid in oleItems
                dispItem = oleItems[clsid+1]
            else
                dispItem = DispatchItem(refType, refAttr, doc)
                oleItems[clsid(dispItem)+1] = dispItem
            end
            coclass_clsid(dispItem) = clsid(coclass)
            if flags & IMPLTYPEFLAG_FSOURCE(pythoncom)
                bIsSink(dispItem) = 1
                sources[clsid(dispItem)+1] = (dispItem, flags)
            else
                interfaces[clsid(dispItem)+1] = (dispItem, flags)
            end
            if clsid ∉ vtableItems && refAttr[12] & TYPEFLAG_FDUAL(pythoncom)
                refType = GetRefTypeInfo(refType, GetRefTypeOfImplType(refType, -1))
                refAttr = GetTypeAttr(refType)
                @assert(typekind(refAttr) == TKIND_INTERFACE(pythoncom))
                vtableItem = VTableItem(refType, refAttr, doc)
                vtableItems[clsid+1] = vtableItem
            end
        end
    end
    sources(coclass) = collect(values(sources))
    interfaces(coclass) = collect(values(interfaces))
end

function _Build_Interface(self::Generator, type_info_tuple)::Tuple
    info, infotype, doc, attr = type_info_tuple
    oleItem = nothing
    vtableItem = nothing
    if infotype == TKIND_DISPATCH(pythoncom) ||
       infotype == TKIND_INTERFACE(pythoncom) &&
       attr[12] & TYPEFLAG_FDISPATCHABLE(pythoncom)
        oleItem = DispatchItem(info, attr, doc)
        if wTypeFlags(attr) & TYPEFLAG_FDUAL(pythoncom)
            refhtype = GetRefTypeOfImplType(info, -1)
            info = GetRefTypeInfo(info, refhtype)
            attr = GetTypeAttr(info)
            infotype = TKIND_INTERFACE(pythoncom)
        else
            infotype = nothing
        end
    end
    @assert(infotype in [nothing, TKIND_INTERFACE(pythoncom)])
    if infotype == TKIND_INTERFACE(pythoncom)
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
        if infotype == TKIND_ENUM(pythoncom) || infotype == TKIND_MODULE(pythoncom)
            newItem = EnumerationItem(info, attr, doc)
            enumItems[newItem.doc[1]+1] = newItem
        elseif infotype in [TKIND_DISPATCH(pythoncom), TKIND_INTERFACE(pythoncom)]
            if clsid ∉ oleItems
                oleItem, vtableItem = _Build_Interface(self, type_info_tuple)
                oleItems[clsid+1] = oleItem
                if vtableItem != nothing
                    vtableItems[clsid+1] = vtableItem
                end
            end
        elseif infotype == TKIND_RECORD(pythoncom) || infotype == TKIND_UNION(pythoncom)
            newItem = RecordItem(info, attr, doc)
            recordItems[newItem.clsid+1] = newItem
        elseif infotype == TKIND_ALIAS(pythoncom)
            continue
        elseif infotype == TKIND_COCLASS(pythoncom)
            newItem, child_infos = _Build_CoClass(self, type_info_tuple)
            _Build_CoClassChildren(self, newItem, child_infos, oleItems, vtableItems)
            oleItems[newItem.clsid+1] = newItem
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
    write(self.file, "python_version = 0x%x", (hexversion(sys),))
    println(self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    println(self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    println(self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    write(self.file)
    println(self.file)
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
        println(stream)
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
        if clsid(record) == IID_NULL(pythoncom)
            write(
                stream,
                "\t###%s: %s, # Record disabled because it doesn\'t have a non-null GUID",
                (repr(doc(record)[1]), repr(string(clsid(record)))),
            )
        else
            write(stream, "\t%s: %s,", (repr(doc(record)[1]), repr(string(clsid(record)))))
        end
    end
    write(stream)
    println(stream)
    if self.generate_type == GEN_FULL
        write(stream)
        for item in values(oleItems)
            if item != nothing && bWritten(item)
                write(stream, "\t\'%s\' : %s,", (string(clsid(item)), python_name(item)))
            end
        end
        write(stream)
        write(stream)
        write(stream)
        write(stream)
        write(stream)
        for item in values(vtableItems)
            write(stream, "\t\'%s\' : \'%s\',", (clsid(item), python_name(item)))
        end
        write(stream)
        println(stream)
    else
        write(stream)
        write(stream)
        for item in values(oleItems)
            if item != nothing
                write(
                    stream,
                    "\t\'%s\' : %s,",
                    (string(clsid(item)), repr(python_name(item))),
                )
            end
        end
        write(stream)
        write(stream)
        write(stream)
        for item in values(vtableItems)
            write(stream, "\t\'%s\' : \'%s\',", (clsid(item), python_name(item)))
        end
        write(stream)
        println(stream)
    end
    println(stream)
    map = Dict()
    for item in values(oleItems)
        if item != nothing && !isa(item, CoClassItem)
            map[python_name(item)+1] = clsid(item)
        end
    end
    for item in values(vtableItems)
        map[python_name(item)+1] = clsid(item)
    end
    write(stream)
    for (name, iid) in items(map)
        write(stream, "\t\'%s\' : \'%s\',", (name, iid))
    end
    write(stream)
    println(stream)
    if enumItems
        write(stream)
    end
    println(stream)
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
            if infotype == TKIND_COCLASS(pythoncom)
                coClassItem, child_infos = _Build_CoClass(self, type_info_tuple)
                found = __init__(build.MakePublicAttributeName, doc[1]) == child
                if !(found)
                    for (info, info_type, refType, doc, refAttr, flags) in child_infos
                        if __init__(build.MakePublicAttributeName, doc[1]) == child
                            found = 1
                            break
                        end
                    end
                end
                if found
                    oleItems[clsid(coClassItem)+1] = coClassItem
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
                if infotype in [TKIND_INTERFACE(pythoncom), TKIND_DISPATCH(pythoncom)]
                    if __init__(build.MakePublicAttributeName, doc[1]) == child
                        found = 1
                        oleItem, vtableItem = _Build_Interface(self, type_info_tuple)
                        oleItems[clsid+1] = oleItem
                        if vtableItem != nothing
                            vtableItems[clsid+1] = vtableItem
                        end
                    end
                end
            end
        end
        @assert(found)
        items = Dict()
        for (key, value) in items(oleItems)
            items[key+1] = (value, nothing)
        end
        for (key, value) in items(vtableItems)
            existing = get(items, key, nothing)
            if existing != nothing
                new_val = (existing[1], value)
            else
                new_val = (nothing, value)
            end
            items[key+1] = new_val
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
    if bWritten(oleitem)
        write(
            self.file,
            "win32com_.client.CLSIDToClass.RegisterCLSID( \"%s\", %s )",
            (clsid(oleitem), python_name(oleitem)),
        )
    end
end

function checkWriteDispatchBaseClass(self::Generator)
    if !(self.bHaveWrittenDispatchBaseClass)
        write(self.file)
        self.bHaveWrittenDispatchBaseClass = 1
    end
end

function checkWriteCoClassBaseClass(self::Generator)
    if !(self.bHaveWrittenCoClassBaseClass)
        write(self.file)
        self.bHaveWrittenCoClassBaseClass = 1
    end
end

function checkWriteEventBaseClass(self::Generator)
    if !(self.bHaveWrittenEventBaseClass)
        self.bHaveWrittenEventBaseClass = 1
    end
end

function main()
    println("This is a worker module.  Please use makepy to generate Python files.")
end

main()
end
