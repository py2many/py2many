abstract type AbstractCDispatch <: Abstractdynamic.CDispatch end
abstract type AbstractConstants end
abstract type AbstractEventsProxy end
abstract type AbstractDispatchBaseClass end
abstract type AbstractCoClassBaseClass end
abstract type AbstractVARIANT <: Abstractobject end
import pythoncom
include("dynamic.jl")
include("gencache.jl")

import pywintypes
_PyIDispatchType = pythoncom.TypeIIDs[pythoncom.IID_IDispatch+1]
function __WrapDispatch(
    dispatch,
    userName = nothing,
    resultCLSID = nothing,
    typeinfo = nothing,
    UnicodeToString = nothing,
    clsctx = pythoncom.CLSCTX_SERVER,
    WrapperClass = nothing,
)
    @assert(UnicodeToString === nothing)
    if resultCLSID === nothing
        try
            typeinfo = GetTypeInfo(dispatch)
            if typeinfo != nothing
                resultCLSID = string(GetTypeAttr(typeinfo)[1])
            end
        catch exn
            if exn isa (pythoncom.com_error, AttributeError)
                #= pass =#
            end
        end
    end
    if resultCLSID != nothing
        include("gencache.jl")
        klass = GetClassForCLSID(gencache, resultCLSID)
        if klass != nothing
            return klass(dispatch)
        end
    end
    if WrapperClass === nothing
        WrapperClass = CDispatch
    end
    return Dispatch(dynamic, dispatch, userName, WrapperClass, typeinfo)
end

function GetObject(Pathname = nothing, Class = nothing, clsctx = nothing)
    if clsctx === nothing
        clsctx = pythoncom.CLSCTX_ALL
    end
    if Pathname === nothing && Class === nothing || Pathname != nothing && Class != nothing
        throw(ValueError("You must specify a value for Pathname or Class, but not both."))
    end
    if Class != nothing
        return GetActiveObject(Class, clsctx)
    else
        return Moniker(Pathname, clsctx)
    end
end

function GetActiveObject(Class, clsctx = pythoncom.CLSCTX_ALL)
    resultCLSID = IID(pywintypes, Class)
    dispatch = GetActiveObject(pythoncom, resultCLSID)
    dispatch = QueryInterface(dispatch, pythoncom.IID_IDispatch)
    return __WrapDispatch(dispatch, Class)
end

function Moniker(Pathname, clsctx = pythoncom.CLSCTX_ALL)
    moniker, i, bindCtx = MkParseDisplayName(pythoncom, Pathname)
    dispatch = BindToObject(moniker, bindCtx, nothing, pythoncom.IID_IDispatch)
    return __WrapDispatch(dispatch, Pathname)
end

function Dispatch(
    dispatch,
    userName = nothing,
    resultCLSID = nothing,
    typeinfo = nothing,
    UnicodeToString = nothing,
    clsctx = pythoncom.CLSCTX_SERVER,
)
    @assert(UnicodeToString === nothing)
    dispatch, userName = _GetGoodDispatchAndUserName(dynamic, dispatch, userName, clsctx)
    return __WrapDispatch(dispatch, userName, resultCLSID, typeinfo)
end

function DispatchEx(
    clsid,
    machine = nothing,
    userName = nothing,
    resultCLSID = nothing,
    typeinfo = nothing,
    UnicodeToString = nothing,
    clsctx = nothing,
)
    @assert(UnicodeToString === nothing)
    if clsctx === nothing
        clsctx = pythoncom.CLSCTX_SERVER
        if machine != nothing
            clsctx = clsctx & ~(pythoncom.CLSCTX_INPROC)
        end
    end
    if machine === nothing
        serverInfo = nothing
    else
        serverInfo = (machine,)
    end
    if userName === nothing
        userName = clsid
    end
    dispatch = CoCreateInstanceEx(
        pythoncom,
        clsid,
        nothing,
        clsctx,
        serverInfo,
        (pythoncom.IID_IDispatch,),
    )[1]
    return Dispatch(dispatch, userName, resultCLSID, typeinfo)
end

mutable struct CDispatch <: AbstractCDispatch

end
function _wrap_dispatch_(
    self::AbstractCDispatch,
    ob,
    userName = nothing,
    returnCLSID = nothing,
    UnicodeToString = nothing,
)
    @assert(UnicodeToString === nothing)
    return Dispatch(ob, userName, returnCLSID, nothing)
end

function __dir__(self::AbstractCDispatch)
    return __dir__(dynamic.CDispatch)
end

function CastTo(ob, target, typelib = nothing)
    mod = nothing
    if typelib != nothing
        mod = MakeModuleForTypelib(
            gencache,
            clsid(typelib),
            lcid(typelib),
            parse(Int, major(typelib)),
            parse(Int, minor(typelib)),
        )
        if !hasattr(mod, target)
            throw(
                ValueError(
                    "The interface name \'%s\' does not appear in the specified library %r" %
                    (target, ver_desc(typelib)),
                ),
            )
        end
    elseif hasattr(target, "index")
    elseif "CLSID"
        not in __dict__(ob.__class__)
        ob = EnsureDispatch(gencache, ob)
    elseif "CLSID"
        not in __dict__(ob.__class__)
        throw(ValueError("Must be a makepy-able object for this to work"))
        clsid = CLSID(ob)
        mod = GetModuleForCLSID(gencache, clsid)
        mod = GetModuleForTypelib(
            gencache,
            CLSID(mod),
            LCID(mod),
            MajorVersion(mod),
            MinorVersion(mod),
        )
        target_clsid = get(mod.NamesToIIDMap, target)
    elseif target_clsid === nothing
        throw(
            ValueError(
                "The interface name \'%s\' does not appear in the same library as object \'%r\'" %
                (target, ob),
            ),
        )
        mod = GetModuleForCLSID(gencache, target_clsid)
    end
    if mod != nothing
        target_class = getattr(mod, target)
        target_class = getattr(target_class, "default_interface", target_class)
        return target_class(ob)
    end
    throw(ValueError)
end

mutable struct Constants <: AbstractConstants
    __dicts__::Any
end
function __getattr__(self::AbstractConstants, a)
    for d in self.__dicts__
        if a in d
            return d[a+1]
        end
    end
    throw(AttributeError(a))
end

constants = Constants()
function _event_setattr_(self, attr, val)
    try
        __setattr__(self.__class__.__bases__[1], self, attr, val)
    catch exn
        if exn isa AttributeError
            self.__dict__[attr] = val
        end
    end
end

mutable struct EventsProxy <: AbstractEventsProxy
    _obj_::Any
    __dict__::Any

    EventsProxy(_obj_::Any, __dict__::Any = ob) = new(_obj_, __dict__)
end
function __del__(self::AbstractEventsProxy)
    try
        close(self._obj_)
    catch exn
        if exn isa pythoncom.com_error
            #= pass =#
        end
    end
end

function __getattr__(self::AbstractEventsProxy, attr)
    return getattr(self._obj_, attr)
end

function __setattr__(self::AbstractEventsProxy, attr, val)
    setattr(self._obj_, attr, val)
end

function DispatchWithEvents(clsid, user_event_class)::EventsProxy
    disp = Dispatch(clsid)
    if !get(disp.__class__.__dict__, "CLSID")
        try
            ti = GetTypeInfo(disp._oleobj_)
            disp_clsid = GetTypeAttr(ti)[1]
            tlb, index = GetContainingTypeLib(ti)
            tla = GetLibAttr(tlb)
            EnsureModule(gencache, tla[1], tla[2], tla[4], tla[5], 0)
            disp_class = GetClassForProgID(gencache, string(disp_clsid))
        catch exn
            if exn isa pythoncom.com_error
                throw(
                    TypeError(
                        "This COM object can not automate the makepy process - please run makepy manually for this object",
                    ),
                )
            end
        end
    else
        disp_class = __class__(disp)
    end
    clsid = CLSID(disp_class)
    try
        using types: ClassType
    catch exn
        if exn isa ImportError
            new_type = type_
        end
    end
    events_class = getevents(clsid)
    if events_class === nothing
        throw(ValueError("This COM object does not support events."))
    end
    result_class = new_type(
        "COMEventClass",
        (disp_class, events_class, user_event_class),
        Dict("__setattr__" => _event_setattr_),
    )
    instance = result_class(_oleobj_(disp))
    __init__(events_class, instance, instance)
    if hasattr(user_event_class, "__init__")
        __init__(user_event_class, instance)
    end
    return EventsProxy(instance)
end

function WithEvents(disp, user_event_class)
    disp = Dispatch(disp)
    if !get(disp.__class__.__dict__, "CLSID")
        try
            ti = GetTypeInfo(disp._oleobj_)
            disp_clsid = GetTypeAttr(ti)[1]
            tlb, index = GetContainingTypeLib(ti)
            tla = GetLibAttr(tlb)
            EnsureModule(gencache, tla[1], tla[2], tla[4], tla[5], 0)
            disp_class = GetClassForProgID(gencache, string(disp_clsid))
        catch exn
            if exn isa pythoncom.com_error
                throw(
                    TypeError(
                        "This COM object can not automate the makepy process - please run makepy manually for this object",
                    ),
                )
            end
        end
    else
        disp_class = __class__(disp)
    end
    clsid = CLSID(disp_class)
    try
        using types: ClassType
    catch exn
        if exn isa ImportError
            new_type = type_
        end
    end
    events_class = getevents(clsid)
    if events_class === nothing
        throw(ValueError("This COM object does not support events."))
    end
    result_class = new_type("COMEventClass", (events_class, user_event_class), Dict())
    instance = result_class(disp)
    if hasattr(user_event_class, "__init__")
        __init__(user_event_class, instance)
    end
    return instance
end

function getevents(clsid)
    clsid = string(IID(pywintypes, clsid))
    klass = GetClassForCLSID(gencache, clsid)
    try
        return default_source(klass)
    catch exn
        if exn isa AttributeError
            try
                return default_source(gencache.GetClassForCLSID(klass.coclass_clsid))
            catch exn
                if exn isa AttributeError
                    return nothing
                end
            end
        end
    end
end

function Record(name, object)
    include("gencache.jl")
    object = EnsureDispatch(gencache, object)
    module_ = modules(sys)[__module__(object.__class__)+1]
    package = GetModuleForTypelib(
        gencache,
        CLSID(module_),
        LCID(module_),
        MajorVersion(module_),
        MinorVersion(module_),
    )
    try
        struct_guid = RecordMap(package)[name+1]
    catch exn
        if exn isa KeyError
            throw(
                ValueError(
                    "The structure \'%s\' is not defined in module \'%s\'" %
                    (name, package),
                ),
            )
        end
    end
    return GetRecordFromGuids(
        pythoncom,
        CLSID(module_),
        MajorVersion(module_),
        MinorVersion(module_),
        LCID(module_),
        struct_guid,
    )
end

mutable struct DispatchBaseClass <: AbstractDispatchBaseClass
    Properties_::Any
    __class__::Any
    __dict__::Any
    _oleobj_::Any
    oobj::Any

    DispatchBaseClass(oobj = nothing) = begin
        if oobj === nothing
            oobj = pythoncom.new(self.CLSID)
        elseif isa(oobj, DispatchBaseClass)
            try
                oobj = oobj._oleobj_.QueryInterface(self.CLSID, pythoncom.IID_IDispatch)
            catch exn
                let details = exn
                    if details isa pythoncom.com_error
                        import winerror
                    elseif details.hresult != winerror.E_NOINTERFACE
                        error()
                        oobj = oobj._oleobj_
                    end
                end
            end
        end
        new(oobj = nothing)
    end
end
function __dir__(self::AbstractDispatchBaseClass)::Vector
    lst =
        (
            (collect(keys(self.__dict__)) + dir(self.__class__)) +
            collect(keys(self._prop_map_get_))
        ) + collect(keys(self._prop_map_put_))
    try
        lst += [Name(p) for p in self.Properties_]
    catch exn
        if exn isa AttributeError
            #= pass =#
        end
    end
    return collect(set(lst))
end

function __repr__(self::AbstractDispatchBaseClass)
    try
        mod_doc = __doc__(sys.modules[self.__class__.__module__+1])
        if mod_doc
            mod_name = "win32com.gen_py." + mod_doc
        else
            mod_name = __name__(sys.modules[self.__class__.__module__+1])
        end
    catch exn
        if exn isa KeyError
            mod_name = "win32com.gen_py.unknown"
        end
    end
    return "<%s.%s instance at 0x%s>" % (mod_name, self.__class__.__name__, id(self))
end

function __eq__(self::AbstractDispatchBaseClass, other)::Bool
    other = getattr(other, "_oleobj_", other)
    return self._oleobj_ == other
end

function __ne__(self::AbstractDispatchBaseClass, other)::Bool
    other = getattr(other, "_oleobj_", other)
    return self._oleobj_ != other
end

function _ApplyTypes_(
    self::AbstractDispatchBaseClass,
    dispid,
    wFlags,
    retType,
    argTypes,
    user,
    resultCLSID,
)
    return _get_good_object_(
        self,
        InvokeTypes(self._oleobj_, dispid, 0, wFlags, retType, argTypes, args...),
        user,
        resultCLSID,
    )
end

function __getattr__(self::AbstractDispatchBaseClass, attr)
    args = get(self._prop_map_get_, attr)
    if args === nothing
        throw(AttributeError("\'%s\' object has no attribute \'%s\'" % (repr(self), attr)))
    end
    return _ApplyTypes_(self, args...)
end

function __setattr__(self::AbstractDispatchBaseClass, attr, value)
    if attr in self.__dict__
        self.__dict__[attr] = value
        return
    end
    try
        args, defArgs = self._prop_map_put_[attr+1]
    catch exn
        if exn isa KeyError
            throw(
                AttributeError(
                    "\'%s\' object has no attribute \'%s\'" % (repr(self), attr),
                ),
            )
        end
    end
    Invoke(self._oleobj_, (args + (value,)) + defArgs...)
end

function _get_good_single_object_(
    self::AbstractDispatchBaseClass,
    obj,
    obUserName = nothing,
    resultCLSID = nothing,
)
    return _get_good_single_object_(obj, obUserName, resultCLSID)
end

function _get_good_object_(
    self::AbstractDispatchBaseClass,
    obj,
    obUserName = nothing,
    resultCLSID = nothing,
)
    return _get_good_object_(obj, obUserName, resultCLSID)
end

function _get_good_single_object_(obj, obUserName = nothing, resultCLSID = nothing)
    if _PyIDispatchType == type_(obj)
        return Dispatch(obj, obUserName, resultCLSID)
    end
    return obj
end

function _get_good_object_(obj, obUserName = nothing, resultCLSID = nothing)::Tuple
    if obj === nothing
        return nothing
    elseif isa(obj, tuple)
        obUserNameTuple = repeat([(obUserName,)...], length(obj))
        resultCLSIDTuple = repeat([(resultCLSID,)...], length(obj))
        return tuple(map(_get_good_object_, obj, obUserNameTuple, resultCLSIDTuple))
    else
        return _get_good_single_object_(obj, obUserName, resultCLSID)
    end
end

mutable struct CoClassBaseClass <: AbstractCoClassBaseClass
    __class__::Any
    __dict__::Any
    dispobj::Any
    oobj::Any

    CoClassBaseClass(oobj = nothing) = begin
        if oobj === nothing
            oobj = pythoncom.new(self.CLSID)
        end
        for maybe in
            ["__call__", "__str__", "__int__", "__iter__", "__len__", "__nonzero__"]
            if hasattr(dispobj, maybe)
                setattr(self, maybe, getattr(self, "__maybe" + maybe))
            end
        end
        new(oobj = nothing)
    end
end
function __repr__(self::AbstractCoClassBaseClass)
    return "<win32com.gen_py.%s.%s>" % (__doc__, self.__class__.__name__)
end

function __getattr__(self::AbstractCoClassBaseClass, attr)
    d = self.__dict__["_dispobj_"]
    if d != nothing
        return getattr(d, attr)
    end
    throw(AttributeError(attr))
end

function __setattr__(self::AbstractCoClassBaseClass, attr, value)
    if attr in self.__dict__
        self.__dict__[attr] = value
        return
    end
    try
        d = self.__dict__["_dispobj_"]
        if d != nothing
            __setattr__(d, attr, value)
            return
        end
    catch exn
        if exn isa AttributeError
            #= pass =#
        end
    end
    self.__dict__[attr] = value
end

function __maybe__call__(self::AbstractCoClassBaseClass)
    return __call__(self.__dict__["_dispobj_"], args..., kwargs)
end

function __maybe__str__(self::AbstractCoClassBaseClass)
    return __str__(self.__dict__["_dispobj_"], args...)
end

function __maybe__int__(self::AbstractCoClassBaseClass)
    return __int__(self.__dict__["_dispobj_"], args...)
end

function __maybe__iter__(self::AbstractCoClassBaseClass)
    return __iter__(self.__dict__["_dispobj_"])
end

function __maybe__len__(self::AbstractCoClassBaseClass)
    return __len__(self.__dict__["_dispobj_"])
end

function __maybe__nonzero__(self::AbstractCoClassBaseClass)
    return __nonzero__(self.__dict__["_dispobj_"])
end

mutable struct VARIANT <: AbstractVARIANT
    _value::Any
    varianttype::Any
    value::Any

    VARIANT(
        _value::Any,
        varianttype::Any,
        value::Any = property(_get_value, _set_value, _del_value),
    ) = new(_value, varianttype, value)
end
function _get_value(self::AbstractVARIANT)
    return self._value
end

function _set_value(self::AbstractVARIANT, newval)
    self._value = _get_good_object_(newval)
end

function _del_value(self::AbstractVARIANT)
    self._value!
end

function __repr__(self::AbstractVARIANT)
    return "win32com.client.VARIANT(%r, %r)" % (self.varianttype, self._value)
end
