using Printf
using PyCall
pythoncom = pyimport("pythoncom")
#= Support for dynamic COM client support.

Introduction
 Dynamic COM client support is the ability to use a COM server without
 prior knowledge of the server.  This can be used to talk to almost all
 COM servers, including much of MS Office.

 In general, you should not use this module directly - see below.

Example
 >>> import win32com.client
 >>> xl = win32com.client.Dispatch("Excel.Application")
 # The line above invokes the functionality of this class.
 # xl is now an object we can use to talk to Excel.
 >>> xl.Visible = 1 # The Excel window becomes visible.

 =#




import winerror
include("build.jl")
using pywintypes: IIDType
import win32com.client
import win32com.client
abstract type AbstractCDispatch end
abstract type AbstractFactory end
debugging = 0
debugging_attr = 0
LCID = 0
ERRORS_BAD_CONTEXT = [
    winerror.DISP_E_MEMBERNOTFOUND,
    winerror.DISP_E_BADPARAMCOUNT,
    winerror.DISP_E_PARAMNOTOPTIONAL,
    winerror.DISP_E_TYPEMISMATCH,
    winerror.E_INVALIDARG,
]
ALL_INVOKE_TYPES = [
    INVOKE_PROPERTYGET(pythoncom),
    INVOKE_PROPERTYPUT(pythoncom),
    INVOKE_PROPERTYPUTREF(pythoncom),
    INVOKE_FUNC(pythoncom),
]
function debug_print()
    if debugging != 0
        for arg in args

        end
        println()
    end
end

function debug_attr_print()
    if debugging_attr != 0
        for arg in args

        end
        println()
    end
end

function MakeMethod(func, inst, cls)
    return MethodType(types, func, inst)
end

PyIDispatchType = TypeIIDs(pythoncom)[IID_IDispatch(pythoncom)+1]
PyIUnknownType = TypeIIDs(pythoncom)[IID_IUnknown(pythoncom)+1]
_GoodDispatchTypes = (str, IIDType)
_defaultDispatchItem = build.DispatchItem
function _GetGoodDispatch(IDispatch, clsctx = CLSCTX_SERVER(pythoncom))
    if isa(IDispatch, PyIDispatchType)
        return IDispatch
    end
    if isa(IDispatch, _GoodDispatchTypes)
        try
            IDispatch = connect(pythoncom, IDispatch)
        catch exn
            if exn isa ole_error(pythoncom)
                IDispatch = CoCreateInstance(
                    pythoncom,
                    IDispatch,
                    nothing,
                    clsctx,
                    IID_IDispatch(pythoncom),
                )
            end
        end
    else
        IDispatch = getattr(IDispatch, "_oleobj_", IDispatch)
    end
    return IDispatch
end

function _GetGoodDispatchAndUserName(IDispatch, userName, clsctx)::Tuple
    if userName === nothing
        if isa(IDispatch, str)
            userName = IDispatch
        end
    else
        userName = string(userName)
    end
    return (_GetGoodDispatch(IDispatch, clsctx), userName)
end

function _GetDescInvokeType(entry, invoke_type)
    if !(entry) || !desc(entry)
        return invoke_type
    end
    if desckind(entry.desc) == DESCKIND_VARDESC(pythoncom)
        return invoke_type
    end
    return invkind(entry.desc)
end

function Dispatch(
    IDispatch,
    userName = nothing,
    createClass = nothing,
    typeinfo = nothing,
    UnicodeToString = nothing,
    clsctx = CLSCTX_SERVER(pythoncom),
)
    @assert(UnicodeToString === nothing)
    IDispatch, userName = _GetGoodDispatchAndUserName(IDispatch, userName, clsctx)
    if createClass === nothing
        createClass = CDispatch
    end
    lazydata = nothing
    try
        if typeinfo === nothing
            typeinfo = GetTypeInfo(IDispatch)
        end
        if typeinfo != nothing
            try
                typecomp = GetTypeComp(typeinfo)
                lazydata = (typeinfo, typecomp)
            catch exn
                if exn isa com_error(pythoncom)
                    #= pass =#
                end
            end
        end
    catch exn
        if exn isa com_error(pythoncom)
            typeinfo = nothing
        end
    end
    olerepr = MakeOleRepr(IDispatch, typeinfo, lazydata)
    return createClass(IDispatch, olerepr, userName, lazydata)
end

function MakeOleRepr(IDispatch, typeinfo, typecomp)
    olerepr = nothing
    if typeinfo != nothing
        try
            attr = GetTypeAttr(typeinfo)
            if attr[6] == TKIND_INTERFACE(pythoncom) && attr[12] & TYPEFLAG_FDUAL(pythoncom)
                href = GetRefTypeOfImplType(typeinfo, -1)
                typeinfo = GetRefTypeInfo(typeinfo, href)
                attr = GetTypeAttr(typeinfo)
            end
            if typecomp === nothing
                olerepr = DispatchItem(build, typeinfo, attr, nothing, 0)
            else
                olerepr = LazyDispatchItem(build, attr, nothing)
            end
        catch exn
            if exn isa ole_error(pythoncom)
                #= pass =#
            end
        end
    end
    if olerepr === nothing
        olerepr = DispatchItem(build)
    end
    return olerepr
end

function DumbDispatch(
    IDispatch,
    userName = nothing,
    createClass = nothing,
    UnicodeToString = nothing,
    clsctx = CLSCTX_SERVER(pythoncom),
)
    #= Dispatch with no type info =#
    @assert(UnicodeToString === nothing)
    IDispatch, userName = _GetGoodDispatchAndUserName(IDispatch, userName, clsctx)
    if createClass === nothing
        createClass = CDispatch
    end
    return createClass(IDispatch, DispatchItem(build), userName)
end

mutable struct CDispatch <: AbstractCDispatch
    ob::Any
    _olerepr_::Any
    _username_::Any
    Properties_::Any
    _oleobj_::Any
    __dict__::Any
    _mapCachedItems_::Any
    _enum_::Any
    _lazydata_::Any
    _builtMethods_::Any
    __class__::Any

    CDispatch(
        IDispatch,
        olerepr,
        userName = nothing,
        UnicodeToString = nothing,
        lazydata = nothing,
    ) = begin
        @assert(UnicodeToString === nothing)
        if userName === nothing
            userName = "<unknown>"
        end
        new(IDispatch, olerepr, userName, UnicodeToString, lazydata)
    end
end
function __call__(self::CDispatch)::Tuple
    #= Provide 'default dispatch' COM functionality - allow instance to be called =#
    if self._olerepr_.defaultDispatchName
        invkind, dispid = _find_dispatch_type_(self, self._olerepr_.defaultDispatchName)
    else
        invkind, dispid = (
            DISPATCH_METHOD(pythoncom) | DISPATCH_PROPERTYGET(pythoncom),
            DISPID_VALUE(pythoncom),
        )
    end
    if invkind != nothing
        allArgs = (dispid, LCID, invkind, 1) + args
        return _get_good_object_(
            self,
            Invoke(self._oleobj_, allArgs...),
            self._olerepr_.defaultDispatchName,
            nothing,
        )
    end
    throw(TypeError("This dispatch object does not define a default method"))
end

function __bool__(self::CDispatch)::Bool
    return true
end

function __repr__(self::CDispatch)
    return "<COMObject %s>" % self._username_
end

function __str__(self::CDispatch)::String
    try
        return string(__call__(self))
    catch exn
        let details = exn
            if details isa com_error(pythoncom)
                if hresult(details)
                    not in ERRORS_BAD_CONTEXT
                    error()
                end
                return __repr__(self)
            end
        end
    end
end

function __dir__(self::CDispatch)::Vector
    lst = (collect(keys(self.__dict__)) + dir(self.__class__)) + _dir_ole_(self)
    try
        lst += [Name(p) for p in self.Properties_]
    catch exn
        if exn isa AttributeError
            #= pass =#
        end
    end
    return collect(set(lst))
end

function _dir_ole_(self::CDispatch)::Vector
    items_dict = Dict()
    for iTI = 0:GetTypeInfoCount(self._oleobj_)-1
        typeInfo = GetTypeInfo(self._oleobj_, iTI)
        _UpdateWithITypeInfo_(self, items_dict, typeInfo)
    end
    return collect(keys(items_dict))
end

function _UpdateWithITypeInfo_(self::CDispatch, items_dict, typeInfo)
    typeInfos = [typeInfo]
    inspectedIIDs = Dict(IID_IDispatch(pythoncom) => nothing)
    while length(typeInfos) > 0
        typeInfo = pop(typeInfos)
        typeAttr = GetTypeAttr(typeInfo)
        if iid(typeAttr)
            not in keys(inspectedIIDs)
            inspectedIIDs[iid(typeAttr)+1] = nothing
            for iFun = 0:cFuncs(typeAttr)-1
                funDesc = GetFuncDesc(typeInfo, iFun)
                funName = GetNames(typeInfo, memid(funDesc))[1]
                if funName
                    not in items_dict
                    items_dict[funName+1] = nothing
                end
            end
            for iImplType = 0:cImplTypes(typeAttr)-1
                iRefType = GetRefTypeOfImplType(typeInfo, iImplType)
                refTypeInfo = GetRefTypeInfo(typeInfo, iRefType)
                push!(typeInfos, refTypeInfo)
            end
        end
    end
end

function __eq__(self::CDispatch, other)::Bool
    other = getattr(other, "_oleobj_", other)
    return self._oleobj_ == other
end

function __ne__(self::CDispatch, other)::Bool
    other = getattr(other, "_oleobj_", other)
    return self._oleobj_ != other
end

function __int__(self::CDispatch)::Int64
    return parse(Int, __call__(self))
end

function __len__(self::CDispatch)
    invkind, dispid = _find_dispatch_type_(self, "Count")
    if invkind
        return Invoke(self._oleobj_, dispid, LCID, invkind, 1)
    end
    throw(TypeError("This dispatch object does not define a Count method"))
end

function _NewEnum(self::CDispatch)
    try
        invkind = DISPATCH_METHOD(pythoncom) | DISPATCH_PROPERTYGET(pythoncom)
        enum = InvokeTypes(
            self._oleobj_,
            DISPID_NEWENUM(pythoncom),
            LCID,
            invkind,
            (13, 10),
            (),
        )
    catch exn
        if exn isa com_error(pythoncom)
            return nothing
        end
    end
    include("util.jl")
    return WrapEnum(util, enum, nothing)
end

function __getitem__(self::CDispatch, index)::Tuple
    if isa(index, int)
        if self.__dict__["_enum_"] === nothing
            self.__dict__["_enum_"] = _NewEnum(self)
        end
        if self.__dict__["_enum_"] != nothing
            return _get_good_object_(self, __getitem__(self._enum_, index))
        end
    end
    invkind, dispid = _find_dispatch_type_(self, "Item")
    if invkind != nothing
        return _get_good_object_(
            self,
            Invoke(self._oleobj_, dispid, LCID, invkind, 1, index),
        )
    end
    throw(TypeError("This object does not support enumeration"))
end

function __setitem__(self::CDispatch, index)::Tuple
    if self._olerepr_.defaultDispatchName
        invkind, dispid = _find_dispatch_type_(self, self._olerepr_.defaultDispatchName)
    else
        invkind, dispid = (
            DISPATCH_PROPERTYPUT(pythoncom) | DISPATCH_PROPERTYPUTREF(pythoncom),
            DISPID_VALUE(pythoncom),
        )
    end
    if invkind != nothing
        allArgs = (dispid, LCID, invkind, 0, index) + args
        return _get_good_object_(
            self,
            Invoke(self._oleobj_, allArgs...),
            self._olerepr_.defaultDispatchName,
            nothing,
        )
    end
    throw(TypeError("This dispatch object does not define a default method"))
end

function _find_dispatch_type_(self::CDispatch, methodName)::Tuple
    if methodName in self._olerepr_.mapFuncs
        item = self._olerepr_.mapFuncs[methodName+1]
        return (desc(item)[5], dispid(item))
    end
    if methodName in self._olerepr_.propMapGet
        item = self._olerepr_.propMapGet[methodName+1]
        return (desc(item)[5], dispid(item))
    end
    try
        dispid = GetIDsOfNames(self._oleobj_, 0, methodName)
    catch exn
        return (nothing, nothing)
    end
    return (DISPATCH_METHOD(pythoncom) | DISPATCH_PROPERTYGET(pythoncom), dispid)
end

function _ApplyTypes_(
    self::CDispatch,
    dispid,
    wFlags,
    retType,
    argTypes,
    user,
    resultCLSID,
)::Tuple
    result = InvokeTypes(self._oleobj_, (dispid, LCID, wFlags, retType, argTypes) + args...)
    return _get_good_object_(self, result, user, resultCLSID)
end

function _wrap_dispatch_(
    self::CDispatch,
    ob,
    userName = nothing,
    returnCLSID = nothing,
    UnicodeToString = nothing,
)
    @assert(UnicodeToString === nothing)
    return Dispatch(ob, userName)
end

function _get_good_single_object_(
    self::CDispatch,
    ob,
    userName = nothing,
    ReturnCLSID = nothing,
)
    if isa(ob, PyIDispatchType)
        return _wrap_dispatch_(self, ob, userName, ReturnCLSID)
    end
    if isa(ob, PyIUnknownType)
        try
            ob = QueryInterface(ob, IID_IDispatch(pythoncom))
        catch exn
            if exn isa com_error(pythoncom)
                return ob
            end
        end
        return _wrap_dispatch_(self, ob, userName, ReturnCLSID)
    end
    return ob
end

function _get_good_object_(
    self::CDispatch,
    ob,
    userName = nothing,
    ReturnCLSID = nothing,
)::Tuple
    #= Given an object (usually the retval from a method), make it a good object to return.
            Basically checks if it is a COM object, and wraps it up.
            Also handles the fact that a retval may be a tuple of retvals =#
    if ob === nothing
        return nothing
    elseif isa(ob, tuple)
        return tuple(map((o, s, oun, rc) -> _get_good_single_object_(s, o, oun, rc), ob))
    else
        return _get_good_single_object_(self, ob)
    end
end

function _make_method_(self::CDispatch, name)
    #= Make a method object - Assumes in olerepr funcmap =#
    methodName = MakePublicAttributeName(build, name)
    methodCodeList =
        MakeFuncMethod(self._olerepr_, self._olerepr_.mapFuncs[name+1], methodName, 0)
    methodCode = join(methodCodeList, "\n")
    try
        codeObject = compile(methodCode, "<COMObject %s>" % self._username_, "exec")
        tempNameSpace = Dict()
        globNameSpace = copy(globals())
        globNameSpace["Dispatch"] = win32com.client.Dispatch
        exec(codeObject, globNameSpace, tempNameSpace)
        name = methodName
        fn = tempNameSpace[name+1]
        self._builtMethods_[name+1] = tempNameSpace[name+1]
        newMeth = MakeMethod(fn, self, self.__class__)
        return newMeth
    catch exn
        debug_print()
        current_exceptions() != [] ? current_exceptions()[end] : nothing
    end
    return nothing
end

function _Release_(self::CDispatch)
    #= Cleanup object - like a close - to force cleanup when you dont
            want to rely on Python's reference counting. =#
    for childCont in values(self._mapCachedItems_)
        _Release_(childCont)
    end
    self._mapCachedItems_ = Dict()
    if self._oleobj_
        Release(self._oleobj_)
        self.__dict__["_oleobj_"] = nothing
    end
    if self._olerepr_
        self.__dict__["_olerepr_"] = nothing
    end
    self._enum_ = nothing
end

function _proc_(self::CDispatch, name)::Tuple
    #= Call the named method as a procedure, rather than function.
            Mainly used by Word.Basic, which whinges about such things. =#
    try
        item = self._olerepr_.mapFuncs[name+1]
        dispId = dispid(item)
        return _get_good_object_(
            self,
            Invoke(self._oleobj_, (dispId, LCID, desc(item)[5], 0) + args...),
        )
    catch exn
        if exn isa KeyError
            throw(AttributeError(name))
        end
    end
end

function _print_details_(self::CDispatch)
    #= Debug routine - dumps what it knows about an object. =#
    println("AxDispatch container", self._username_)
    try
        println("Methods:")
        for method in keys(self._olerepr_.mapFuncs)
            println("\t", method)
        end
        println("Props:")
        for (prop, entry) in items(self._olerepr_.propMap)
            @printf("\t%s = 0x%x - %s", (prop, dispid(entry), repr(entry)))
        end
        println("Get Props:")
        for (prop, entry) in items(self._olerepr_.propMapGet)
            @printf("\t%s = 0x%x - %s", (prop, dispid(entry), repr(entry)))
        end
        println("Put Props:")
        for (prop, entry) in items(self._olerepr_.propMapPut)
            @printf("\t%s = 0x%x - %s", (prop, dispid(entry), repr(entry)))
        end
    catch exn
        current_exceptions() != [] ? current_exceptions()[end] : nothing
    end
end

function __LazyMap__(self::CDispatch, attr)::Int64
    try
        if _LazyAddAttr_(self, attr)
            debug_attr_print()
            return 1
        end
    catch exn
        if exn isa AttributeError
            return 0
        end
    end
end

function _LazyAddAttr_(self::CDispatch, attr)::Int64
    if self._lazydata_ === nothing
        return 0
    end
    res = 0
    typeinfo, typecomp = self._lazydata_
    olerepr = self._olerepr_
    for i in ALL_INVOKE_TYPES
        try
            x, t = Bind(typecomp, attr, i)
            if x == 0 && attr[begin:3] in ("Set", "Get")
                x, t = Bind(typecomp, attr[4:end], i)
            end
            if x == DESCKIND_FUNCDESC(pythoncom)
                r = _AddFunc_(olerepr, typeinfo, t, 0)
            elseif x == DESCKIND_VARDESC(pythoncom)
                r = _AddVar_(olerepr, typeinfo, t, 0)
            else
                r = nothing
            end
            if !(r === nothing)
                key, map = (r[1], r[2])
                item = map[key+1]
                if map == propMapPut(olerepr)
                    _propMapPutCheck_(olerepr, key, item)
                elseif map == propMapGet(olerepr)
                    _propMapGetCheck_(olerepr, key, item)
                end
                res = 1
            end
        catch exn
            #= pass =#
        end
    end
    return res
end

function _FlagAsMethod(self::CDispatch)
    #= Flag these attribute names as being methods.
            Some objects do not correctly differentiate methods and
            properties, leading to problems when calling these methods.

            Specifically, trying to say: ob.SomeFunc()
            may yield an exception "None object is not callable"
            In this case, an attempt to fetch the *property* has worked
            and returned None, rather than indicating it is really a method.
            Calling: ob._FlagAsMethod("SomeFunc")
            should then allow this to work.
             =#
    for name in methodNames
        details = MapEntry(build, __AttrToID__(self, name), (name,))
        self._olerepr_.mapFuncs[name+1] = details
    end
end

function __AttrToID__(self::CDispatch, attr)
    debug_attr_print()
    return GetIDsOfNames(self._oleobj_, 0, attr)
end

function __getattr__(self::CDispatch, attr)::Tuple
    if attr == "__iter__"
        try
            invkind = DISPATCH_METHOD(pythoncom) | DISPATCH_PROPERTYGET(pythoncom)
            enum = InvokeTypes(
                self._oleobj_,
                DISPID_NEWENUM(pythoncom),
                LCID,
                invkind,
                (13, 10),
                (),
            )
        catch exn
            if exn isa com_error(pythoncom)
                throw(AttributeError("This object can not function as an iterator"))
            end
        end
        mutable struct Factory <: AbstractFactory
            ob::Any
        end
        function __call__(self::Factory)::Factory
            import win32com.client.util
            import win32com.client.util
            import win32com.client.util
            return Iterator(win32com.client.util, self.ob)
        end

        return Factory(enum)
    end
    if startswith(attr, "_") && endswith(attr, "_")
        throw(AttributeError(attr))
    end
    try
        return MakeMethod(self._builtMethods_[attr+1], self, self.__class__)
    catch exn
        if exn isa KeyError
            #= pass =#
        end
    end
    if attr in self._olerepr_.mapFuncs
        return _make_method_(self, attr)
    end
    retEntry = nothing
    if self._olerepr_ && self._oleobj_
        retEntry = get(self._olerepr_.propMap, attr)
        if retEntry === nothing
            retEntry = get(self._olerepr_.propMapGet, attr)
        end
        if retEntry === nothing
            try
                if __LazyMap__(self, attr) != 0
                    if attr in self._olerepr_.mapFuncs
                        return _make_method_(self, attr)
                    end
                    retEntry = get(self._olerepr_.propMap, attr)
                    if retEntry === nothing
                        retEntry = get(self._olerepr_.propMapGet, attr)
                    end
                end
                if retEntry === nothing
                    retEntry = MapEntry(build, __AttrToID__(self, attr), (attr,))
                end
            catch exn
                if exn isa ole_error(pythoncom)
                    #= pass =#
                end
            end
        end
    end
    if retEntry != nothing
        try
            ret = self._mapCachedItems_[dispid(retEntry)+1]
            debug_attr_print()
            return ret
        catch exn
            if exn isa (KeyError, AttributeError)
                debug_attr_print()
            end
        end
    end
    if retEntry != nothing
        invoke_type = _GetDescInvokeType(retEntry, INVOKE_PROPERTYGET(pythoncom))
        debug_attr_print()
        try
            ret = Invoke(self._oleobj_, dispid(retEntry), 0, invoke_type, 1)
        catch exn
            let details = exn
                if details isa com_error(pythoncom)
                    if hresult(details) in ERRORS_BAD_CONTEXT
                        self._olerepr_.mapFuncs[attr+1] = retEntry
                        return _make_method_(self, attr)
                    end
                    error()
                end
            end
        end
        debug_attr_print()
        return _get_good_object_(self, ret)
    end
    throw(AttributeError("%s.%s" % (self._username_, attr)))
end

function __setattr__(self::CDispatch, attr, value)
    if attr in self.__dict__
        self.__dict__[attr] = value
        return
    end
    debug_attr_print()
    if self._olerepr_
        if attr in self._olerepr_.propMap
            entry = self._olerepr_.propMap[attr+1]
            invoke_type = _GetDescInvokeType(entry, INVOKE_PROPERTYPUT(pythoncom))
            Invoke(self._oleobj_, dispid(entry), 0, invoke_type, 0, value)
            return
        end
        if attr in self._olerepr_.propMapPut
            entry = self._olerepr_.propMapPut[attr+1]
            invoke_type = _GetDescInvokeType(entry, INVOKE_PROPERTYPUT(pythoncom))
            Invoke(self._oleobj_, dispid(entry), 0, invoke_type, 0, value)
            return
        end
    end
    if self._oleobj_
        if __LazyMap__(self, attr) != 0
            if attr in self._olerepr_.propMap
                entry = self._olerepr_.propMap[attr+1]
                invoke_type = _GetDescInvokeType(entry, INVOKE_PROPERTYPUT(pythoncom))
                Invoke(self._oleobj_, dispid(entry), 0, invoke_type, 0, value)
                return
            end
            if attr in self._olerepr_.propMapPut
                entry = self._olerepr_.propMapPut[attr+1]
                invoke_type = _GetDescInvokeType(entry, INVOKE_PROPERTYPUT(pythoncom))
                Invoke(self._oleobj_, dispid(entry), 0, invoke_type, 0, value)
                return
            end
        end
        try
            entry = MapEntry(build, __AttrToID__(self, attr), (attr,))
        catch exn
            if exn isa com_error(pythoncom)
                entry = nothing
            end
        end
        if entry != nothing
            try
                invoke_type = _GetDescInvokeType(entry, INVOKE_PROPERTYPUT(pythoncom))
                Invoke(self._oleobj_, dispid(entry), 0, invoke_type, 0, value)
                self._olerepr_.propMap[attr+1] = entry
                debug_attr_print()
                return
            catch exn
                if exn isa com_error(pythoncom)
                    #= pass =#
                end
            end
        end
    end
    throw(AttributeError("Property \'%s.%s\' can not be set." % (self._username_, attr)))
end

