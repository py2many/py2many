abstract type AbstractCoClassItem <: Abstractbuild.OleItem end
abstract type AbstractGeneratorProgress end
abstract type AbstractGenerator end
mutable struct CoClassItem <: build.OleItem
    bWritten::Any
    clsid::Any
    interfaces::Any
    python_name::Any
    sources::Any
    bForUser::Int64
    bIsDispatch::Int64
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
    ) = begin
        build.OleItem.__init__(self, doc)
        new(typeinfo, attr, doc = nothing, sources = [], interfaces = [], bForUser = 1)
    end
end
function WriteClass(self::AbstractCoClassItem, generator)
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
function Starting(self::AbstractGeneratorProgress, tlb_desc)
    self.tlb_desc = tlb_desc
end

function Finished(self::AbstractGeneratorProgress)

end

function SetDescription(self::AbstractGeneratorProgress, desc, maxticks = nothing)

end

function Tick(self::AbstractGeneratorProgress, desc = nothing)

end

function VerboseProgress(self::AbstractGeneratorProgress, desc)

end

function LogWarning(self::AbstractGeneratorProgress, desc)

end

function LogBeginGenerate(self::AbstractGeneratorProgress, filename)
    #= pass =#
end

function Close(self::AbstractGeneratorProgress)
    #= pass =#
end

mutable struct Generator <: AbstractGenerator
    bBuildHidden::Any
    bHaveWrittenCoClassBaseClass::Any
    bHaveWrittenDispatchBaseClass::Any
    bHaveWrittenEventBaseClass::Any
    base_mod_name::Any
    file::Any
    generate_type::Any
    sourceFilename::Any
    typelib::Any
    bUnicodeToString::Any
    progress::Any

    Generator(
        typelib,
        sourceFilename,
        progressObject,
        bBuildHidden = 1,
        bUnicodeToString = nothing,
    ) = begin
        @assert(bUnicodeToString === nothing)
        new(
            typelib,
            sourceFilename,
            progressObject,
            bBuildHidden = 1,
            bUnicodeToString = nothing,
        )
    end
end
function CollectOleItemInfosFromType(self::AbstractGenerator)::Vector
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

function _Build_CoClass(self::AbstractGenerator, type_info_tuple)::Tuple
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
    self::AbstractGenerator,
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
                sources[clsid(dispItem)] = (dispItem, flags)
            else
                interfaces[clsid(dispItem)] = (dispItem, flags)
            end
            if clsid
                not in vtableItems && refAttr[12] & TYPEFLAG_FDUAL(pythoncom)
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

function _Build_Interface(self::AbstractGenerator, type_info_tuple)::Tuple
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

function BuildOleItemsFromType(self::AbstractGenerator)::Tuple
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
            enumItems[doc(newItem)[1]] = newItem
        elseif infotype in [TKIND_DISPATCH(pythoncom), TKIND_INTERFACE(pythoncom)]
            if clsid
                not in oleItems
                oleItem, vtableItem = _Build_Interface(self, type_info_tuple)
                oleItems[clsid] = oleItem
                if vtableItem != nothing
                    vtableItems[clsid] = vtableItem
                end
            end
        elseif infotype == TKIND_RECORD(pythoncom) || infotype == TKIND_UNION(pythoncom)
            newItem = RecordItem(info, attr, doc)
            recordItems[clsid(newItem)] = newItem
        elseif infotype == TKIND_ALIAS(pythoncom)
            continue
        elseif infotype == TKIND_COCLASS(pythoncom)
            newItem, child_infos = _Build_CoClass(self, type_info_tuple)
            _Build_CoClassChildren(self, newItem, child_infos, oleItems, vtableItems)
            oleItems[clsid(newItem)] = newItem
        else
            LogWarning(self.progress, "Unknown TKIND found: %d" % infotype)
        end
    end
    return (oleItems, enumItems, recordItems, vtableItems)
end

function open_writer(self::AbstractGenerator, filename, encoding = "mbcs")
    temp_filename = get_temp_filename(self, filename)
    return readline(temp_filename)
end

function finish_writer(self::AbstractGenerator, filename, f, worked)
    close(f)
    try
        std::fs::remove_file(filename)
    catch exn
        if exn isa error(os)
            #= pass =#
        end
    end
    temp_filename = get_temp_filename(self, filename)
    if worked
        try
            rename(os, temp_filename, filename)
        catch exn
            if exn isa error(os)
                try
                    std::fs::remove_file(filename)
                catch exn
                    if exn isa error(os)
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

function get_temp_filename(self::AbstractGenerator, filename)
    return "%s.%d.temp" % (filename, getpid(os))
end

function generate(self::AbstractGenerator, file, is_for_demand = 0)
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

function do_gen_file_header(self::AbstractGenerator)
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

function do_generate(self::AbstractGenerator)
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
            map[python_name(item)] = clsid(item)
        end
    end
    for item in values(vtableItems)
        map[python_name(item)] = clsid(item)
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

function generate_child(self::AbstractGenerator, child, dir)
    self.generate_type = GEN_DEMAND_CHILD
    la = GetLibAttr(self.typelib)
    lcid = la[2]
    clsid = la[1]
    major = la[4]
    minor = la[5]
    self.base_mod_name =
        ("win32com.gen_py." + string(clsid)[2:-1]) + ("x%sx%sx%s" % (lcid, major, minor))
    try
        oleItems = Dict()
        vtableItems = Dict()
        infos = CollectOleItemInfosFromType(self)
        found = 0
        for type_info_tuple in infos
            info, infotype, doc, attr = type_info_tuple
            if infotype == TKIND_COCLASS(pythoncom)
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
                    oleItems[clsid(coClassItem)] = coClassItem
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

function do_gen_child_item(self::AbstractGenerator, oleitem)
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
            "win32com.client.CLSIDToClass.RegisterCLSID( \"%s\", %s )",
            (clsid(oleitem), python_name(oleitem)),
        )
    end
end

function checkWriteDispatchBaseClass(self::AbstractGenerator)
    if !(self.bHaveWrittenDispatchBaseClass)
        write(self.file)
        self.bHaveWrittenDispatchBaseClass = 1
    end
end

function checkWriteCoClassBaseClass(self::AbstractGenerator)
    if !(self.bHaveWrittenCoClassBaseClass)
        write(self.file)
        self.bHaveWrittenCoClassBaseClass = 1
    end
end

function checkWriteEventBaseClass(self::AbstractGenerator)
    if !(self.bHaveWrittenEventBaseClass)
        self.bHaveWrittenEventBaseClass = 1
    end
end

function main()
    println("This is a worker module.  Please use makepy to generate Python files.")
end

main()
