#= Contains knowledge to build a COM object definition.

This module is used by both the @dynamic@ and @makepy@ modules to build
all knowledge of a COM object.

This module contains classes which contain the actual knowledge of the object.
This include parameter and return type information, the COM dispid and CLSID, etc.

Other modules may use this information to generate .py files, use the information
dynamically, or possibly even generate .html documentation for objects.
 =#
abstract type AbstractNotSupportedException <: AbstractException end
abstract type AbstractMapEntry end
abstract type AbstractOleItem end
abstract type AbstractDispatchItem <: AbstractOleItem end
abstract type AbstractVTableItem <: AbstractDispatchItem end
abstract type AbstractLazyDispatchItem <: AbstractDispatchItem end

import string
using keyword: iskeyword
import pythoncom
using pywintypes: TimeType
import winerror
import Dates
function _makeDocString(s)
    if version_info(sys) < (3,)
        s = Vector{UInt8}(s)
    end
    return repr(s)
end

error = "PythonCOM.Client.Build error"
mutable struct NotSupportedException <: AbstractNotSupportedException

end

DropIndirection = "DropIndirection"
NoTranslateTypes = [
    pythoncom.VT_BOOL,
    pythoncom.VT_CLSID,
    pythoncom.VT_CY,
    pythoncom.VT_DATE,
    pythoncom.VT_DECIMAL,
    pythoncom.VT_EMPTY,
    pythoncom.VT_ERROR,
    pythoncom.VT_FILETIME,
    pythoncom.VT_HRESULT,
    pythoncom.VT_I1,
    pythoncom.VT_I2,
    pythoncom.VT_I4,
    pythoncom.VT_I8,
    pythoncom.VT_INT,
    pythoncom.VT_NULL,
    pythoncom.VT_R4,
    pythoncom.VT_R8,
    pythoncom.VT_NULL,
    pythoncom.VT_STREAM,
    pythoncom.VT_UI1,
    pythoncom.VT_UI2,
    pythoncom.VT_UI4,
    pythoncom.VT_UI8,
    pythoncom.VT_UINT,
    pythoncom.VT_VOID,
]
NoTranslateMap = Dict()
for v in NoTranslateTypes
    NoTranslateMap[v] = nothing
end
mutable struct MapEntry <: AbstractMapEntry
    doc::Any
    hidden::Any
    names::Any
    resultCLSID::Any
    resultDocumentation::Any
    resultDoc::Any
    wasProperty::Int64

    MapEntry(
        desc_or_id,
        names = nothing,
        doc = nothing,
        resultCLSID = pythoncom.IID_NULL,
        resultDoc = nothing,
        hidden = 0,
    ) = begin
        if type_(desc_or_id) == type_(0)
            self.dispid = desc_or_id
            self.desc = nothing
        else
            self.dispid = desc_or_id[0]
            self.desc = desc_or_id
        end
        new(
            desc_or_id,
            names = nothing,
            doc = nothing,
            resultCLSID = pythoncom.IID_NULL,
            resultDoc = nothing,
            hidden = 0,
        )
    end
end
function __repr__(self::AbstractMapEntry)
    return test
end

function GetResultCLSID(self::AbstractMapEntry)
    rc = self.resultCLSID
    if rc == pythoncom.IID_NULL
        return nothing
    end
    return rc
end

function GetResultCLSIDStr(self::AbstractMapEntry)::String
    rc = GetResultCLSID(self)
    if rc === nothing
        return "None"
    end
    return repr(string(rc))
end

function GetResultName(self::AbstractMapEntry)
    if self.resultDocumentation === nothing
        return nothing
    end
    return self.resultDocumentation[1]
end

mutable struct OleItem <: AbstractOleItem
    doc::Any
    bIsDispatch::Int64
    bIsSink::Int64
    bWritten::Int64
    clsid::Any
    co_class::Any
    typename::String

    OleItem(doc = nothing) = begin
        if self.doc
            self.python_name = MakePublicAttributeName(self.doc[0])
        else
            self.python_name = nothing
        end
        new(doc = nothing)
    end
end

mutable struct DispatchItem <: AbstractDispatchItem
    bIsDispatch::Any
    clsid::Any
    mapFuncs::Any
    propMapGet::Any
    propMapPut::Any
    attr::Any
    bForUser::Int64
    defaultDispatchName::Any
    doc::Any
    hidden::Int64
    propMap::Dict
    typeinfo::Any
    typename::String

    DispatchItem(typeinfo = nothing, attr = nothing, doc = nothing, bForUser = 1) = begin
        OleItem.__init__(self, doc)
        if typeinfo
            self.Build(typeinfo, attr, bForUser)
        end
        new(typeinfo = nothing, attr = nothing, doc = nothing, bForUser = 1)
    end
end
function _propMapPutCheck_(self::AbstractDispatchItem, key, item)
    ins, outs, opts = CountInOutOptArgs(self, desc(item)[3])
    if ins > 1
        if (opts + 1) === ins || ins == (desc(item)[7] + 1)
            newKey = "Set" + key
            deleteExisting = 0
        else
            deleteExisting = 1
            if key in self.mapFuncs || key in self.propMapGet
                newKey = "Set" + key
            else
                newKey = key
            end
        end
        wasProperty(item) = 1
        self.mapFuncs[newKey+1] = item
        if deleteExisting
            #Delete Unsupported
            del(self.propMapPut)
        end
    end
end

function _propMapGetCheck_(self::AbstractDispatchItem, key, item)
    ins, outs, opts = CountInOutOptArgs(self, desc(item)[3])
    if ins > 0
        if desc(item)[7] === ins || ins === opts
            newKey = "Get" + key
            deleteExisting = 0
        else
            deleteExisting = 1
            if key in self.mapFuncs
                newKey = "Get" + key
            else
                newKey = key
            end
        end
        wasProperty(item) = 1
        self.mapFuncs[newKey+1] = item
        if deleteExisting
            #Delete Unsupported
            del(self.propMapGet)
        end
    end
end

function _AddFunc_(self::AbstractDispatchItem, typeinfo, fdesc, bForUser)::Tuple
    @assert(desckind(fdesc) == pythoncom.DESCKIND_FUNCDESC)
    id = memid(fdesc)
    funcflags = wFuncFlags(fdesc)
    try
        names = GetNames(typeinfo, id)
        name = names[1]
    catch exn
        if exn isa pythoncom.ole_error
            name = ""
            names = nothing
        end
    end
    doc = nothing
    try
        if bForUser
            doc = GetDocumentation(typeinfo, id)
        end
    catch exn
        if exn isa pythoncom.ole_error
            #= pass =#
        end
    end
    if id == 0 && name
        self.defaultDispatchName = name
    end
    invkind = invkind(fdesc)
    typerepr, flag, defval = rettype(fdesc)
    typerepr, resultCLSID, resultDoc = _ResolveType(typerepr, typeinfo)
    rettype(fdesc) = (typerepr, flag, defval, resultCLSID)
    argList = []
    for argDesc in args(fdesc)
        typerepr, flag, defval = argDesc
        arg_type, arg_clsid, arg_doc = _ResolveType(typerepr, typeinfo)
        argDesc = (arg_type, flag, defval, arg_clsid)
        push!(argList, argDesc)
    end
    args(fdesc) = tuple(argList)
    hidden = (funcflags & pythoncom.FUNCFLAG_FHIDDEN) != 0
    if invkind == pythoncom.INVOKE_PROPERTYGET
        map = self.propMapGet
    elseif invkind in (pythoncom.INVOKE_PROPERTYPUT, pythoncom.INVOKE_PROPERTYPUTREF)
        existing = get(self.propMapPut, name, nothing)
        if existing != nothing
            if desc(existing)[5] == pythoncom.INVOKE_PROPERTYPUT
                map = self.mapFuncs
                name = "Set" * name
            else
                wasProperty(existing) = 1
                self.mapFuncs["Set"*name+1] = existing
                map = self.propMapPut
            end
        else
            map = self.propMapPut
        end
    elseif invkind == pythoncom.INVOKE_FUNC
        map = self.mapFuncs
    else
        map = nothing
    end
    if !(map === nothing)
        map[name+1] = MapEntry(fdesc, names, doc, resultCLSID, resultDoc, hidden)
        if funckind(fdesc) != pythoncom.FUNC_DISPATCH
            return nothing
        end
        return (name, map)
    end
    return nothing
end

function _AddVar_(self::AbstractDispatchItem, typeinfo, vardesc, bForUser)::Tuple
    @assert(desckind(vardesc) == pythoncom.DESCKIND_VARDESC)
    if varkind(vardesc) == pythoncom.VAR_DISPATCH
        id = memid(vardesc)
        names = GetNames(typeinfo, id)
        typerepr, flags, defval = elemdescVar(vardesc)
        typerepr, resultCLSID, resultDoc = _ResolveType(typerepr, typeinfo)
        elemdescVar(vardesc) = (typerepr, flags, defval)
        doc = nothing
        try
            if bForUser
                doc = GetDocumentation(typeinfo, id)
            end
        catch exn
            if exn isa pythoncom.ole_error
                #= pass =#
            end
        end
        map = self.propMap
        hidden = (wVarFlags(vardesc) & 64) != 0
        map[names[1]+1] = MapEntry(vardesc, names, doc, resultCLSID, resultDoc, hidden)
        return (names[1], map)
    else
        return nothing
    end
end

function Build(self::AbstractDispatchItem, typeinfo, attr, bForUser = 1)
    self.clsid = attr[1]
    self.bIsDispatch = (wTypeFlags(attr) & pythoncom.TYPEFLAG_FDISPATCHABLE) != 0
    if typeinfo === nothing
        return
    end
    for j = 0:attr[7]-1
        fdesc = GetFuncDesc(typeinfo, j)
        _AddFunc_(self, typeinfo, fdesc, bForUser)
    end
    for j = 0:attr[8]-1
        fdesc = GetVarDesc(typeinfo, j)
        _AddVar_(self, typeinfo, fdesc, bForUser)
    end
    for (key, item) in collect(items(self.propMapGet))
        _propMapGetCheck_(self, key, item)
    end
    for (key, item) in collect(items(self.propMapPut))
        _propMapPutCheck_(self, key, item)
    end
end

function CountInOutOptArgs(self::AbstractDispatchItem, argTuple)::Tuple
    ins = 0
    out = 0
    opts = 0
    for argCheck in argTuple
        inOut = argCheck[2]
        if inOut == 0
            ins = ins + 1
            out = out + 1
        else
            if inOut & pythoncom.PARAMFLAG_FIN
                ins = ins + 1
            end
            if inOut & pythoncom.PARAMFLAG_FOPT
                opts = opts + 1
            end
            if inOut & pythoncom.PARAMFLAG_FOUT
                out = out + 1
            end
        end
    end
    return (ins, out, opts)
end

function MakeFuncMethod(self::AbstractDispatchItem, entry, name, bMakeClass = 1)::Vector
    if desc(entry) != nothing && length(desc(entry)) < 6 || desc(entry)[7] != -1
        return MakeDispatchFuncMethod(self, entry, name, bMakeClass)
    else
        return MakeVarArgsFuncMethod(self, entry, name, bMakeClass)
    end
end

function MakeDispatchFuncMethod(
    self::AbstractDispatchItem,
    entry,
    name,
    bMakeClass = 1,
)::Vector
    fdesc = desc(entry)
    doc = doc(entry)
    names = names(entry)
    ret = []
    if bMakeClass
        linePrefix = "\t"
        defNamedOptArg = "defaultNamedOptArg"
        defNamedNotOptArg = "defaultNamedNotOptArg"
        defUnnamedArg = "defaultUnnamedArg"
    else
        linePrefix = ""
        defNamedOptArg = "pythoncom.Missing"
        defNamedNotOptArg = "pythoncom.Missing"
        defUnnamedArg = "pythoncom.Missing"
    end
    defOutArg = "pythoncom.Missing"
    id = fdesc[1]
    s =
        ((linePrefix + "def ") + name) *
        "(self" *
        BuildCallList(
            fdesc,
            names,
            defNamedOptArg,
            defNamedNotOptArg,
            defUnnamedArg,
            defOutArg,
        ) *
        "):"
    push!(ret, s)
    if doc && doc[2]
        push!(ret, (linePrefix + "\t") + _makeDocString(doc[2]))
    end
    resclsid = GetResultCLSID(entry)
    if resclsid
        resclsid = "\'%s\'" % resclsid
    else
        resclsid = "None"
    end
    retDesc = fdesc[9][begin:2]
    argsDesc = tuple([what[begin:2] for what in fdesc[3]])
    param_flags = [what[2] for what in fdesc[3]]
    bad_params = [
        flag for flag in param_flags if
        (flag & (pythoncom.PARAMFLAG_FOUT | pythoncom.PARAMFLAG_FRETVAL)) != 0
    ]
    s = nothing
    if length(bad_params) == 0 && length(retDesc) == 2 && retDesc[2] == 0
        rd = retDesc[1]
        if rd in NoTranslateMap
            s =
                "%s\treturn self._oleobj_.InvokeTypes(%d, LCID, %s, %s, %s%s)" %
                (linePrefix, id, fdesc[5], retDesc, argsDesc, _BuildArgList(fdesc, names))
        elseif rd in [pythoncom.VT_DISPATCH, pythoncom.VT_UNKNOWN]
            s =
                "%s\tret = self._oleobj_.InvokeTypes(%d, LCID, %s, %s, %s%s)\n" % (
                    linePrefix,
                    id,
                    fdesc[5],
                    retDesc,
                    repr(argsDesc),
                    _BuildArgList(fdesc, names),
                )
            s = s + ("%s\tif ret is not None:\n" % (linePrefix,))
            if rd == pythoncom.VT_UNKNOWN
                s =
                    s + (
                        "%s\t\t# See if this IUnknown is really an IDispatch\n" %
                        (linePrefix,)
                    )
                s = s + ("%s\t\ttry:\n" % (linePrefix,))
                s =
                    s + (
                        "%s\t\t\tret = ret.QueryInterface(pythoncom.IID_IDispatch)\n" %
                        (linePrefix,)
                    )
                s = s + ("%s\t\texcept pythoncom.error:\n" % (linePrefix,))
                s = s + ("%s\t\t\treturn ret\n" % (linePrefix,))
            end
            s =
                s +
                ("%s\t\tret = Dispatch(ret, %s, %s)\n" % (linePrefix, repr(name), resclsid))
            s = s + ("%s\treturn ret" % linePrefix)
        elseif rd == pythoncom.VT_BSTR
            s = "%s\t# Result is a Unicode object\n" % (linePrefix,)
            s =
                s + (
                    "%s\treturn self._oleobj_.InvokeTypes(%d, LCID, %s, %s, %s%s)" % (
                        linePrefix,
                        id,
                        fdesc[5],
                        retDesc,
                        repr(argsDesc),
                        _BuildArgList(fdesc, names),
                    )
                )
        end
    end
    if s === nothing
        s =
            "%s\treturn self._ApplyTypes_(%d, %s, %s, %s, %s, %s%s)" % (
                linePrefix,
                id,
                fdesc[5],
                retDesc,
                argsDesc,
                repr(name),
                resclsid,
                _BuildArgList(fdesc, names),
            )
    end
    push!(ret, s)
    push!(ret, "")
    return ret
end

function MakeVarArgsFuncMethod(
    self::AbstractDispatchItem,
    entry,
    name,
    bMakeClass = 1,
)::Vector
    fdesc = desc(entry)
    names = names(entry)
    doc = doc(entry)
    ret = []
    argPrefix = "self"
    if bMakeClass
        linePrefix = "\t"
    else
        linePrefix = ""
    end
    push!(ret, ((linePrefix + "def ") + name) * "(" * argPrefix * ", *args):")
    if doc && doc[2]
        push!(ret, (linePrefix + "\t") + _makeDocString(doc[2]))
    end
    if fdesc
        invoketype = fdesc[5]
    else
        invoketype = pythoncom.DISPATCH_METHOD
    end
    s = linePrefix + "\treturn self._get_good_object_(self._oleobj_.Invoke(*(("
    push!(
        ret,
        s * string(dispid(entry)) + (",0,%d,1)+args)),\'%s\')" % (invoketype, names[1])),
    )
    push!(ret, "")
    return ret
end

mutable struct VTableItem <: AbstractVTableItem
    vtableFuncs::Any
end
function Build(self::AbstractVTableItem, typeinfo, attr, bForUser = 1)
    Build(DispatchItem, self, typeinfo, attr)
    @assert(typeinfo != nothing)
    meth_list = append!(
        append!(collect(values(self.mapFuncs)), collect(values(self.propMapGet))),
        collect(values(self.propMapPut)),
    )
    sort(meth_list, (m) -> desc(m)[8])
    self.vtableFuncs = []
    for entry in meth_list
        append(self.vtableFuncs, (names(entry), dispid(entry), desc(entry)))
    end
end

mutable struct LazyDispatchItem <: AbstractLazyDispatchItem
    clsid::Any
    typename::String

    LazyDispatchItem(attr, doc) = begin
        DispatchItem.__init__(self, nothing, attr, doc, 0)
        new(attr, doc)
    end
end

typeSubstMap = Dict(
    pythoncom.VT_INT => pythoncom.VT_I4,
    pythoncom.VT_UINT => pythoncom.VT_UI4,
    pythoncom.VT_HRESULT => pythoncom.VT_I4,
)
function _ResolveType(typerepr, itypeinfo)::Tuple
    if type_(typerepr) == tuple
        indir_vt, subrepr = typerepr
        if indir_vt == pythoncom.VT_PTR
            was_user = type_(subrepr) == tuple && subrepr[1] == pythoncom.VT_USERDEFINED
            subrepr, sub_clsid, sub_doc = _ResolveType(subrepr, itypeinfo)
            if was_user &&
               subrepr in [pythoncom.VT_DISPATCH, pythoncom.VT_UNKNOWN, pythoncom.VT_RECORD]
                return (subrepr, sub_clsid, sub_doc)
            end
            return (subrepr | pythoncom.VT_BYREF, sub_clsid, sub_doc)
        end
        if indir_vt == pythoncom.VT_SAFEARRAY
            subrepr, sub_clsid, sub_doc = _ResolveType(subrepr, itypeinfo)
            return (pythoncom.VT_ARRAY | subrepr, sub_clsid, sub_doc)
        end
        if indir_vt == pythoncom.VT_CARRAY
            return (pythoncom.VT_CARRAY, nothing, nothing)
        end
        if indir_vt == pythoncom.VT_USERDEFINED
            try
                resultTypeInfo = GetRefTypeInfo(itypeinfo, subrepr)
            catch exn
                let details = exn
                    if details isa pythoncom.com_error
                        if hresult(details) in [
                            winerror.TYPE_E_CANTLOADLIBRARY,
                            winerror.TYPE_E_LIBNOTREGISTERED,
                        ]
                            return (pythoncom.VT_UNKNOWN, nothing, nothing)
                        end
                        error()
                    end
                end
            end
            resultAttr = GetTypeAttr(resultTypeInfo)
            typeKind = typekind(resultAttr)
            if typeKind == pythoncom.TKIND_ALIAS
                tdesc = tdescAlias(resultAttr)
                return _ResolveType(tdesc, resultTypeInfo)
            elseif typeKind in [pythoncom.TKIND_ENUM, pythoncom.TKIND_MODULE]
                return (pythoncom.VT_I4, nothing, nothing)
            elseif typeKind == pythoncom.TKIND_DISPATCH
                clsid = GetTypeAttr(resultTypeInfo)[1]
                retdoc = GetDocumentation(resultTypeInfo, -1)
                return (pythoncom.VT_DISPATCH, clsid, retdoc)
            elseif typeKind in [pythoncom.TKIND_INTERFACE, pythoncom.TKIND_COCLASS]
                clsid = GetTypeAttr(resultTypeInfo)[1]
                retdoc = GetDocumentation(resultTypeInfo, -1)
                return (pythoncom.VT_UNKNOWN, clsid, retdoc)
            elseif typeKind == pythoncom.TKIND_RECORD
                return (pythoncom.VT_RECORD, nothing, nothing)
            end
            throw(NotSupportedException("Can not resolve alias or user-defined type"))
        end
    end
    return (get(typeSubstMap, typerepr, typerepr), nothing, nothing)
end

function _BuildArgList(fdesc, names)::Union[str, Any]
    numArgs = max(fdesc[7], length(fdesc[3]))
    names = collect(names)
    while nothing in names
        i = index(names, nothing)
        names[i+1] = "arg%d" % (i,)
    end
    names = collect(map(MakePublicAttributeName, names[2:numArgs+1]))
    name_num = 0
    while length(names) < numArgs
        append(names, "arg%d" % (length(names),))
    end
    for i = 0:5:length(names)-1
        names[i+1] = names[i+1] + "\n\t\t\t"
    end
    return "," + join(names, ", ")
end

valid_identifier_chars = (string.ascii_letters + string.digits) + "_"
function demunge_leading_underscores(className)::Any
    i = 0
    while className[i+1] == "_"
        i += 1
    end
    @assert(i >= 2)
    return className[i:end] + className[begin:i-1]
end

function MakePublicAttributeName(className, is_global = false)::Any
    if className[begin:2] == "__"
        return demunge_leading_underscores(className)
    elseif className == "None"
        className = "NONE"
    elseif iskeyword(className)
        ret = capitalize(className)
        if ret == className
            ret = upper(ret)
        end
        return ret
    elseif is_global && hasattr(__builtins__, className)
        ret = capitalize(className)
        if ret == className
            ret = upper(ret)
        end
        return ret
    end
    return join([char for char in className if char in valid_identifier_chars], "")
end

function MakeDefaultArgRepr(defArgVal)::Union[str, Any]
    try
        inOut = defArgVal[2]
    catch exn
        if exn isa IndexError
            inOut = pythoncom.PARAMFLAG_FIN
        end
    end
    if inOut & pythoncom.PARAMFLAG_FHASDEFAULT
        val = defArgVal[3]
        if isa(val, datetime.datetime)
            return repr(tuple(utctimetuple(val)))
        end
        if type_(val) == TimeType
            year = year(val)
            month = month(val)
            day = day(val)
            hour = hour(val)
            minute = minute(val)
            second = second(val)
            msec = msec(val)
            return "pywintypes.Time((%(year)d, %(month)d, %(day)d, %(hour)d, %(minute)d, %(second)d,0,0,0,%(msec)d))" %
                   locals()
        end
        return repr(val)
    end
    return nothing
end

function BuildCallList(
    fdesc,
    names,
    defNamedOptArg,
    defNamedNotOptArg,
    defUnnamedArg,
    defOutArg,
    is_comment = false,
)::String
    numArgs = length(fdesc[3])
    numOptArgs = fdesc[7]
    strval = ""
    if numOptArgs == -1
        firstOptArg = numArgs
        numArgs = numArgs - 1
    else
        firstOptArg = numArgs - numOptArgs
    end
    for arg = 0:numArgs-1
        try
            argName = names[arg+2]
            namedArg = argName != nothing
        catch exn
            if exn isa IndexError
                namedArg = 0
            end
        end
        if !(namedArg)
            argName = "arg%d" % arg
        end
        thisdesc = fdesc[3][arg+1]
        defArgVal = MakeDefaultArgRepr(thisdesc)
        if defArgVal === nothing
            if (thisdesc[2] & (pythoncom.PARAMFLAG_FOUT | pythoncom.PARAMFLAG_FIN)) ==
               pythoncom.PARAMFLAG_FOUT
                defArgVal = defOutArg
            elseif namedArg
                if arg >= firstOptArg
                    defArgVal = defNamedOptArg
                else
                    defArgVal = defNamedNotOptArg
                end
            else
                defArgVal = defUnnamedArg
            end
        end
        argName = MakePublicAttributeName(argName)
        if ((arg + 1) % 5) == 0
            strval = strval * "\n"
            if is_comment
                strval = strval * "#"
            end
            strval = strval * "\t\t\t"
        end
        strval = strval * ", " + argName
        if defArgVal
            strval = strval * "=" + defArgVal
        end
    end
    if numOptArgs == -1
        strval = strval * ", *" + names[end]
    end
    return strval
end

function main()
    println("Use \'makepy.py\' to generate Python code - this module is just a helper")
end

main()
