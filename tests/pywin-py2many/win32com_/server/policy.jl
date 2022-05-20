#= Policies 

Note that Dispatchers are now implemented in "dispatcher.py", but
are still documented here.

Policies

 A policy is an object which manages the interaction between a public 
 Python object, and COM .  In simple terms, the policy object is the 
 object which is actually called by COM, and it invokes the requested 
 method, fetches/sets the requested property, etc.  See the 
 @win32com_.server.policy.CreateInstance@ method for a description of
 how a policy is specified or created.

 Exactly how a policy determines which underlying object method/property 
 is obtained is up to the policy.  A few policies are provided, but you 
 can build your own.  See each policy class for a description of how it 
 implements its policy.

 There is a policy that allows the object to specify exactly which 
 methods and properties will be exposed.  There is also a policy that 
 will dynamically expose all Python methods and properties - even those 
 added after the object has been instantiated.

Dispatchers

 A Dispatcher is a level in front of a Policy.  A dispatcher is the 
 thing which actually receives the COM calls, and passes them to the 
 policy object (which in turn somehow does something with the wrapped 
 object).

 It is important to note that a policy does not need to have a dispatcher.
 A dispatcher has the same interface as a policy, and simply steps in its 
 place, delegating to the real policy.  The primary use for a Dispatcher 
 is to support debugging when necessary, but without imposing overheads 
 when not (ie, by not using a dispatcher at all).

 There are a few dispatchers provided - "tracing" dispatchers which simply 
 prints calls and args (including a variation which uses 
 win32api.OutputDebugString), and a "debugger" dispatcher, which can 
 invoke the debugger when necessary.

Error Handling

 It is important to realise that the caller of these interfaces may
 not be Python.  Therefore, general Python exceptions and tracebacks aren't 
 much use.

 In general, there is an Exception class that should be raised, to allow 
 the framework to extract rich COM type error information.

 The general rule is that the **only** exception returned from Python COM 
 Server code should be an Exception instance.  Any other Python exception 
 should be considered an implementation bug in the server (if not, it 
 should be handled, and an appropriate Exception instance raised).  Any 
 other exception is considered "unexpected", and a dispatcher may take 
 special action (see Dispatchers above)

 Occasionally, the implementation will raise the policy.error error.  
 This usually means there is a problem in the implementation that the 
 Python programmer should fix.

 For example, if policy is asked to wrap an object which it can not 
 support (because, eg, it does not provide _public_methods_ or _dynamic_) 
 then policy.error will be raised, indicating it is a Python programmers 
 problem, rather than a COM error.

 =#
using OrderedCollections
using PyCall
pythoncom = pyimport("pythoncom")
pywintypes = pyimport("pywintypes")
win32api = pyimport("win32api")
using win32com_.util: IIDToInterfaceName
using win32com_: universal
import win32com_.client
__author__ = "Greg Stein and Mark Hammond"

import winerror

import win32con

S_OK = 0
IDispatchType = pythoncom.TypeIIDs[pythoncom.IID_IDispatch+1]
abstract type AbstractBasicWrapPolicy end
abstract type AbstractMappedWrapPolicy <: AbstractBasicWrapPolicy end
abstract type AbstractDesignatedWrapPolicy <: AbstractMappedWrapPolicy end
abstract type AbstractEventHandlerPolicy <: AbstractDesignatedWrapPolicy end
abstract type AbstractDynamicPolicy <: AbstractBasicWrapPolicy end
IUnknownType = pythoncom.TypeIIDs[pythoncom.IID_IUnknown+1]
using exception: COMException
error = __name__ + " error"
regSpec = "CLSID\\%s\\PythonCOM"
regPolicy = "CLSID\\%s\\PythonCOMPolicy"
regDispatcher = "CLSID\\%s\\PythonCOMDispatcher"
regAddnPath = "CLSID\\%s\\PythonCOMPath"
function CreateInstance(clsid, reqIID)
    #= Create a new instance of the specified IID

        The COM framework **always** calls this function to create a new
        instance for the specified CLSID.  This function looks up the
        registry for the name of a policy, creates the policy, and asks the
        policy to create the specified object by calling the _CreateInstance_ method.

        Exactly how the policy creates the instance is up to the policy.  See the
        specific policy documentation for more details.
         =#
    try
        addnPaths = split(
            RegQueryValue(win32api, win32con.HKEY_CLASSES_ROOT, regAddnPath % clsid),
            ";",
        )
        for newPath in addnPaths
            if newPath ∉ sys.path
                insert(sys.path, 0, newPath)
            end
        end
    catch exn
        if exn isa win32api.error
            #= pass =#
        end
    end
    try
        policy = RegQueryValue(win32api, win32con.HKEY_CLASSES_ROOT, regPolicy % clsid)
        policy = resolve_func(policy)
    catch exn
        if exn isa win32api.error
            policy = DefaultPolicy
        end
    end
    try
        dispatcher =
            RegQueryValue(win32api, win32con.HKEY_CLASSES_ROOT, regDispatcher % clsid)
        if dispatcher
            dispatcher = resolve_func(dispatcher)
        end
    catch exn
        if exn isa win32api.error
            dispatcher = nothing
        end
    end
    if dispatcher
        retObj = dispatcher(policy, nothing)
    else
        retObj = policy(nothing)
    end
    return _CreateInstance_(retObj, clsid, reqIID)
end

mutable struct BasicWrapPolicy <: AbstractBasicWrapPolicy
    #= The base class of policies.

        Normally not used directly (use a child class, instead)

        This policy assumes we are wrapping another object
        as the COM server.  This supports the delegation of the core COM entry points
        to either the wrapped object, or to a child class.

        This policy supports the following special attributes on the wrapped object

        _query_interface_ -- A handler which can respond to the COM 'QueryInterface' call.
        _com_interfaces_ -- An optional list of IIDs which the interface will assume are
            valid for the object.
        _invoke_ -- A handler which can respond to the COM 'Invoke' call.  If this attribute
            is not provided, then the default policy implementation is used.  If this attribute
            does exist, it is responsible for providing all required functionality - ie, the
            policy _invoke_ method is not invoked at all (and nor are you able to call it!)
        _getidsofnames_ -- A handler which can respond to the COM 'GetIDsOfNames' call.  If this attribute
            is not provided, then the default policy implementation is used.  If this attribute
            does exist, it is responsible for providing all required functionality - ie, the
            policy _getidsofnames_ method is not invoked at all (and nor are you able to call it!)

        IDispatchEx functionality:

        _invokeex_ -- Very similar to _invoke_, except slightly different arguments are used.
            And the result is just the _real_ result (rather than the (hresult, argErr, realResult)
            tuple that _invoke_ uses.
            This is the new, prefered handler (the default _invoke_ handler simply called _invokeex_)
        _getdispid_ -- Very similar to _getidsofnames_, except slightly different arguments are used,
            and only 1 property at a time can be fetched (which is all we support in getidsofnames anyway!)
            This is the new, prefered handler (the default _invoke_ handler simply called _invokeex_)
        _getnextdispid_- uses self._name_to_dispid_ to enumerate the DISPIDs
         =#
    _name_to_dispid_::Dict
    _query_interface_
    _invoke_
    _invokeex_
    _getidsofnames_
    _getdispid_
    _com_interfaces_::Vector

    BasicWrapPolicy(object) = begin
        if object != nothing
            _wrap_(object)
        end
        new(object)
    end
end
function _CreateInstance_(self::BasicWrapPolicy, clsid, reqIID)
    #= Creates a new instance of a **wrapped** object

            This method looks up a "@win32com_.server.policy.regSpec@" % clsid entry
            in the registry (using @DefaultPolicy@)
             =#
    try
        classSpec = RegQueryValue(win32api, win32con.HKEY_CLASSES_ROOT, regSpec % clsid)
    catch exn
        if exn isa win32api.error
            throw(
                error(
                    "The object is not correctly registered - %s key can not be read" %
                    (regSpec % clsid),
                ),
            )
        end
    end
    myob = call_func(classSpec)
    _wrap_(self, myob)
    try
        return WrapObject(pythoncom, self, reqIID)
    catch exn
        let xxx_todo_changeme = exn
            if xxx_todo_changeme isa pythoncom.com_error
                hr, desc, exc, arg = xxx_todo_changeme.args
                desc =
                    "The object \'%r\' was created, but does not support the interface \'%s\'(%s): %s" %
                    (myob, IIDToInterfaceName(reqIID), reqIID, desc)
                throw(com_error(pythoncom, hr, desc, exc, arg))
            end
        end
    end
end

function _wrap_(self::BasicWrapPolicy, object)
    #= Wraps up the specified object.

            This function keeps a reference to the passed
            object, and may interogate it to determine how to respond to COM requests, etc.
             =#
    self._name_to_dispid_ = Dict()
    ob = object
    self._obj_ = object
    if hasfield(typeof(ob), :_query_interface_)
        self._query_interface_ = ob._query_interface_
    end
    if hasfield(typeof(ob), :_invoke_)
        self._invoke_ = ob._invoke_
    end
    if hasfield(typeof(ob), :_invokeex_)
        self._invokeex_ = ob._invokeex_
    end
    if hasfield(typeof(ob), :_getidsofnames_)
        self._getidsofnames_ = ob._getidsofnames_
    end
    if hasfield(typeof(ob), :_getdispid_)
        self._getdispid_ = ob._getdispid_
    end
    if hasfield(typeof(ob), :_com_interfaces_)
        self._com_interfaces_ = []
        for i in ob._com_interfaces_
            if type_(i) != pywintypes.IIDType
                if i[1] != "{"
                    i = pythoncom.InterfaceNames[i+1]
                else
                    i = MakeIID(pythoncom, i)
                end
            end
            append(self._com_interfaces_, i)
        end
    else
        self._com_interfaces_ = []
    end
end

function _QueryInterface_(self::BasicWrapPolicy, iid)::Int64
    #= The main COM entry-point for QueryInterface.

            This checks the _com_interfaces_ attribute and if the interface is not specified
            there, it calls the derived helper _query_interface_
             =#
    if iid ∈ self._com_interfaces_
        return 1
    end
    return _query_interface_(self, iid)
end

function _query_interface_(self::BasicWrapPolicy, iid)::Int64
    #= Called if the object does not provide the requested interface in _com_interfaces_,
            and does not provide a _query_interface_ handler.

            Returns a result to the COM framework indicating the interface is not supported.
             =#
    return 0
end

function _Invoke_(self::BasicWrapPolicy, dispid, lcid, wFlags, args)
    #= The main COM entry-point for Invoke.

            This calls the _invoke_ helper.
             =#
    if type_(dispid) == type_("")
        try
            dispid = self._name_to_dispid_[lower(dispid)]
        catch exn
            if exn isa KeyError
                throw(COMException(winerror.DISP_E_MEMBERNOTFOUND, "Member not found"))
            end
        end
    end
    return _invoke_(self, dispid, lcid, wFlags, args)
end

function _invoke_(self::BasicWrapPolicy, dispid, lcid, wFlags, args)
    return (S_OK, -1, _invokeex_(self, dispid, lcid, wFlags, args, nothing, nothing))
end

function _GetIDsOfNames_(self::BasicWrapPolicy, names, lcid)
    #= The main COM entry-point for GetIDsOfNames.

            This checks the validity of the arguments, and calls the _getidsofnames_ helper.
             =#
    if length(names) > 1
        throw(COMException(winerror.DISP_E_INVALID, "Cannot support member argument names"))
    end
    return _getidsofnames_(self, names, lcid)
end

function _getidsofnames_(self::BasicWrapPolicy, names, lcid)::Tuple
    return (_getdispid_(self, names[1], 0),)
end

function _GetDispID_(self::BasicWrapPolicy, name, fdex)
    return _getdispid_(self, name, fdex)
end

function _getdispid_(self::BasicWrapPolicy, name, fdex)::Dict
    try
        return self._name_to_dispid_[lower(name)]
    catch exn
        if exn isa KeyError
            throw(COMException(winerror.DISP_E_UNKNOWNNAME))
        end
    end
end

function _InvokeEx_(
    self::BasicWrapPolicy,
    dispid,
    lcid,
    wFlags,
    args,
    kwargs,
    serviceProvider,
)
    #= The main COM entry-point for InvokeEx.

            This calls the _invokeex_ helper.
             =#
    if type_(dispid) == type_("")
        try
            dispid = self._name_to_dispid_[lower(dispid)]
        catch exn
            if exn isa KeyError
                throw(COMException(winerror.DISP_E_MEMBERNOTFOUND, "Member not found"))
            end
        end
    end
    return _invokeex_(self, dispid, lcid, wFlags, args, kwargs, serviceProvider)
end

function _invokeex_(
    self::BasicWrapPolicy,
    dispid,
    lcid,
    wFlags,
    args,
    kwargs,
    serviceProvider,
)
    #= A stub for _invokeex_ - should never be called.

            Simply raises an exception.
             =#
    throw(error("This class does not provide _invokeex_ semantics"))
end

function _DeleteMemberByName_(self::BasicWrapPolicy, name, fdex)
    return _deletememberbyname_(self, name, fdex)
end

function _deletememberbyname_(self::BasicWrapPolicy, name, fdex)
    throw(COMException(winerror.E_NOTIMPL))
end

function _DeleteMemberByDispID_(self::BasicWrapPolicy, id)
    return _deletememberbydispid(self, id)
end

function _deletememberbydispid_(self::BasicWrapPolicy, id)
    throw(COMException(winerror.E_NOTIMPL))
end

function _GetMemberProperties_(self::BasicWrapPolicy, id, fdex)
    return _getmemberproperties_(self, id, fdex)
end

function _getmemberproperties_(self::BasicWrapPolicy, id, fdex)
    throw(COMException(winerror.E_NOTIMPL))
end

function _GetMemberName_(self::BasicWrapPolicy, dispid)
    return _getmembername_(self, dispid)
end

function _getmembername_(self::BasicWrapPolicy, dispid)
    throw(COMException(winerror.E_NOTIMPL))
end

function _GetNextDispID_(self::BasicWrapPolicy, fdex, dispid)::Vector
    return _getnextdispid_(self, fdex, dispid)
end

function _getnextdispid_(self::BasicWrapPolicy, fdex, dispid)::Vector
    ids = collect(values(self._name_to_dispid_))
    sort(ids)
    if DISPID_STARTENUM ∈ ids
        deleteat!(ids, findfirst(isequal(DISPID_STARTENUM), ids))
    end
    if dispid == DISPID_STARTENUM
        return ids[1]
    else
        try
            return ids[findfirst(isequal(dispid), ids)+2]
        catch exn
            if exn isa ValueError
                throw(COMException(winerror.E_UNEXPECTED))
            end
            if exn isa IndexError
                throw(COMException(winerror.S_FALSE))
            end
        end
    end
end

function _GetNameSpaceParent_(self::BasicWrapPolicy)
    return _getnamespaceparent(self)
end

function _getnamespaceparent_(self::BasicWrapPolicy)
    throw(COMException(winerror.E_NOTIMPL))
end

mutable struct MappedWrapPolicy <: AbstractMappedWrapPolicy
    #= Wraps an object using maps to do its magic

        This policy wraps up a Python object, using a number of maps
        which translate from a Dispatch ID and flags, into an object to call/getattr, etc.

        It is the responsibility of derived classes to determine exactly how the
        maps are filled (ie, the derived classes determine the map filling policy.

        This policy supports the following special attributes on the wrapped object

        _dispid_to_func_/_dispid_to_get_/_dispid_to_put_ -- These are dictionaries
          (keyed by integer dispid, values are string attribute names) which the COM
          implementation uses when it is processing COM requests.  Note that the implementation
          uses this dictionary for its own purposes - not a copy - which means the contents of
          these dictionaries will change as the object is used.

         =#
    _dispid_to_func_
    _dispid_to_get_
    _dispid_to_put_
end
function _wrap_(self::MappedWrapPolicy, object)
    _wrap_(BasicWrapPolicy, self)
    ob = self._obj_
    if hasfield(typeof(ob), :_dispid_to_func_)
        self._dispid_to_func_ = ob._dispid_to_func_
    else
        self._dispid_to_func_ = OrderedDict()
    end
    if hasfield(typeof(ob), :_dispid_to_get_)
        self._dispid_to_get_ = ob._dispid_to_get_
    else
        self._dispid_to_get_ = OrderedDict()
    end
    if hasfield(typeof(ob), :_dispid_to_put_)
        self._dispid_to_put_ = ob._dispid_to_put_
    else
        self._dispid_to_put_ = OrderedDict()
    end
end

function _getmembername_(self::MappedWrapPolicy, dispid)
    if dispid ∈ self._dispid_to_func_
        return self._dispid_to_func_[dispid+1]
    elseif dispid ∈ self._dispid_to_get_
        return self._dispid_to_get_[dispid+1]
    elseif dispid ∈ self._dispid_to_put_
        return self._dispid_to_put_[dispid+1]
    else
        throw(COMException(winerror.DISP_E_MEMBERNOTFOUND))
    end
end

mutable struct DesignatedWrapPolicy <: AbstractDesignatedWrapPolicy
    #= A policy which uses a mapping to link functions and dispid

         A MappedWrappedPolicy which allows the wrapped object to specify, via certain
         special named attributes, exactly which methods and properties are exposed.

         All a wrapped object need do is provide the special attributes, and the policy
         will handle everything else.

         Attributes:

         _public_methods_ -- Required, unless a typelib GUID is given -- A list
                      of strings, which must be the names of methods the object
                      provides.  These methods will be exposed and callable
                      from other COM hosts.
         _public_attrs_ A list of strings, which must be the names of attributes on the object.
                      These attributes will be exposed and readable and possibly writeable from other COM hosts.
         _readonly_attrs_ -- A list of strings, which must also appear in _public_attrs.  These
                      attributes will be readable, but not writable, by other COM hosts.
         _value_ -- A method that will be called if the COM host requests the "default" method
                      (ie, calls Invoke with dispid==DISPID_VALUE)
         _NewEnum -- A method that will be called if the COM host requests an enumerator on the
                      object (ie, calls Invoke with dispid==DISPID_NEWENUM.)
                      It is the responsibility of the method to ensure the returned
                      object conforms to the required Enum interface.

        _typelib_guid_ -- The GUID of the typelibrary with interface definitions we use.
        _typelib_version_ -- A tuple of (major, minor) with a default of 1,1
        _typelib_lcid_ -- The LCID of the typelib, default = LOCALE_USER_DEFAULT

         _Evaluate -- Dunno what this means, except the host has called Invoke with dispid==DISPID_EVALUATE!
                      See the COM documentation for details.
         =#
    _typeinfos_
    _obj_
    _dispid_to_func_
    _dispid_to_get_
    _dispid_to_put_
end
function _wrap_(self::DesignatedWrapPolicy, ob)
    tlb_guid =
        (hasfield(typeof(ob), :_typelib_guid_) ? getfield(ob, :_typelib_guid_) : nothing)
    if tlb_guid != nothing
        tlb_major, tlb_minor = (
            hasfield(typeof(ob), :_typelib_version_) ?
            getfield(ob, :_typelib_version_) : (1, 0)
        )
        tlb_lcid =
            (hasfield(typeof(ob), :_typelib_lcid_) ? getfield(ob, :_typelib_lcid_) : 0)
        interfaces = [
            i for i in (
                hasfield(typeof(ob), :_com_interfaces_) ?
                getfield(ob, :_com_interfaces_) : []
            ) if type_(i) != pywintypes.IIDType && !startswith(i, "{")
        ]
        universal_data = RegisterInterfaces(
            universal,
            tlb_guid,
            tlb_lcid,
            tlb_major,
            tlb_minor,
            interfaces,
        )
    else
        universal_data = []
    end
    _wrap_(MappedWrapPolicy, self)
    if !hasfield(typeof(ob), :_public_methods_) && !hasfield(typeof(ob), :_typelib_guid_)
        throw(
            error(
                "Object does not support DesignatedWrapPolicy, as it does not have either _public_methods_ or _typelib_guid_ attributes.",
            ),
        )
    end
    for (dispid, name) in items(self._dispid_to_func_)
        self._name_to_dispid_[lower(name)+1] = dispid
    end
    for (dispid, name) in items(self._dispid_to_get_)
        self._name_to_dispid_[lower(name)+1] = dispid
    end
    for (dispid, name) in items(self._dispid_to_put_)
        self._name_to_dispid_[lower(name)+1] = dispid
    end
    for (dispid, invkind, name) in universal_data
        self._name_to_dispid_[lower(name)+1] = dispid
        if invkind == DISPATCH_METHOD
            self._dispid_to_func_[dispid+1] = name
        elseif invkind ∈ (DISPATCH_PROPERTYPUT, DISPATCH_PROPERTYPUTREF)
            self._dispid_to_put_[dispid+1] = name
        elseif invkind == DISPATCH_PROPERTYGET
            self._dispid_to_get_[dispid+1] = name
        else
            throw(ValueError("unexpected invkind: %d (%s)" % (invkind, name)))
        end
    end
    if hasfield(typeof(ob), :_value_)
        self._dispid_to_get_[__add__(DISPID_VALUE, 1)] = "_value_"
        self._dispid_to_put_[__add__(DISPID_PROPERTYPUT, 1)] = "_value_"
    end
    if hasfield(typeof(ob), :_NewEnum)
        self._name_to_dispid_["_newenum"] = DISPID_NEWENUM
        self._dispid_to_func_[__add__(DISPID_NEWENUM, 1)] = "_NewEnum"
    end
    if hasfield(typeof(ob), :_Evaluate)
        self._name_to_dispid_["_evaluate"] = DISPID_EVALUATE
        self._dispid_to_func_[__add__(DISPID_EVALUATE, 1)] = "_Evaluate"
    end
    next_dispid = _allocnextdispid(self, 999)
    if hasfield(typeof(ob), :_public_attrs_)
        if hasfield(typeof(ob), :_readonly_attrs_)
            readonly = ob._readonly_attrs_
        else
            readonly = []
        end
        for name in ob._public_attrs_
            dispid = get(self._name_to_dispid_, lower(name))
            if dispid === nothing
                dispid = next_dispid
                self._name_to_dispid_[lower(name)+1] = dispid
                next_dispid = _allocnextdispid(self, next_dispid)
            end
            self._dispid_to_get_[dispid+1] = name
            if name ∉ readonly
                self._dispid_to_put_[dispid+1] = name
            end
        end
    end
    for name in
        (hasfield(typeof(ob), :_public_methods_) ? getfield(ob, :_public_methods_) : [])
        dispid = get(self._name_to_dispid_, lower(name))
        if dispid === nothing
            dispid = next_dispid
            self._name_to_dispid_[lower(name)+1] = dispid
            next_dispid = _allocnextdispid(self, next_dispid)
        end
        self._dispid_to_func_[dispid+1] = name
    end
    self._typeinfos_ = nothing
end

function _build_typeinfos_(self::DesignatedWrapPolicy)::Vector
    tlb_guid = (
        hasfield(typeof(self._obj_), :_typelib_guid_) ?
        getfield(self._obj_, :_typelib_guid_) : nothing
    )
    if tlb_guid === nothing
        return []
    end
    tlb_major, tlb_minor = (
        hasfield(typeof(self._obj_), :_typelib_version_) ?
        getfield(self._obj_, :_typelib_version_) : (1, 0)
    )
    tlb = LoadRegTypeLib(pythoncom, tlb_guid, tlb_major, tlb_minor)
    typecomp = GetTypeComp(tlb)
    for iname in self._obj_._com_interfaces_
        try
            type_info, type_comp = BindType(typecomp, iname)
            if type_info != nothing
                return [type_info]
            end
        catch exn
            if exn isa pythoncom.com_error
                #= pass =#
            end
        end
    end
    return []
end

function _GetTypeInfoCount_(self::DesignatedWrapPolicy)::Int64
    if self._typeinfos_ === nothing
        self._typeinfos_ = _build_typeinfos_(self)
    end
    return length(self._typeinfos_)
end

function _GetTypeInfo_(self::DesignatedWrapPolicy, index, lcid)
    if self._typeinfos_ === nothing
        self._typeinfos_ = _build_typeinfos_(self)
    end
    if index < 0 || index >= length(self._typeinfos_)
        throw(COMException(winerror.DISP_E_BADINDEX))
    end
    return (0, self._typeinfos_[index+1])
end

function _allocnextdispid(self::DesignatedWrapPolicy, last_dispid)
    while true
        last_dispid = last_dispid + 1
        if last_dispid ∉ self._dispid_to_func_ &&
           last_dispid ∉ self._dispid_to_get_ &&
           last_dispid ∉ self._dispid_to_put_
            return last_dispid
        end
    end
end

function _invokeex_(
    self::DesignatedWrapPolicy,
    dispid,
    lcid,
    wFlags,
    args,
    kwArgs,
    serviceProvider,
)
    if __and__(wFlags, DISPATCH_METHOD)
        try
            funcname = self._dispid_to_func_[dispid+1]
        catch exn
            if exn isa KeyError
                if !(__and__(wFlags, DISPATCH_PROPERTYGET))
                    throw(COMException(winerror.DISP_E_MEMBERNOTFOUND))
                end
            end
        end
    end
    if __and__(wFlags, DISPATCH_PROPERTYGET)
        try
            name = self._dispid_to_get_[dispid+1]
        catch exn
            if exn isa KeyError
                throw(COMException(winerror.DISP_E_MEMBERNOTFOUND))
            end
        end
        retob = getfield(self._obj_, :name)
        if type_(retob) == types.MethodType
            retob = retob(args...)
        end
        return retob
    end
    if wFlags & __or__(DISPATCH_PROPERTYPUT, DISPATCH_PROPERTYPUTREF)
        try
            name = self._dispid_to_put_[dispid+1]
        catch exn
            if exn isa KeyError
                throw(COMException(winerror.DISP_E_MEMBERNOTFOUND))
            end
        end
        if type_((
            hasfield(typeof(self._obj_), :name) ? getfield(self._obj_, :name) : nothing
        )) == types.MethodType &&
           type_((
            hasfield(typeof(self._obj_), :Set + name) ? getfield(self._obj_, :Set + name) :
            nothing
        )) == types.MethodType
            fn = getfield(self._obj_, :Set + name)
            fn(args...)
        else
            setattr(self._obj_, name, args[1])
        end
        return
    end
    throw(COMException(winerror.E_INVALIDARG, "invalid wFlags"))
end

mutable struct EventHandlerPolicy <: AbstractEventHandlerPolicy
    #= The default policy used by event handlers in the win32com_.client package.

        In addition to the base policy, this provides argument conversion semantics for
        params
          * dispatch params are converted to dispatch objects.
          * Unicode objects are converted to strings (1.5.2 and earlier)

        NOTE: Later, we may allow the object to override this process??
         =#

end
function _transform_args_(
    self::EventHandlerPolicy,
    args,
    kwArgs,
    dispid,
    lcid,
    wFlags,
    serviceProvider,
)
    ret = []
    for arg in args
        arg_type = type_(arg)
        if arg_type == IDispatchType
            arg = Dispatch(win32com_.client, arg)
        elseif arg_type == IUnknownType
            try
                arg =
                    Dispatch(win32com_.client, QueryInterface(arg, pythoncom.IID_IDispatch))
            catch exn
                if exn isa pythoncom.error
                    #= pass =#
                end
            end
        end
        push!(ret, arg)
    end
    return (tuple(ret), kwArgs)
end

function _invokeex_(
    self::EventHandlerPolicy,
    dispid,
    lcid,
    wFlags,
    args,
    kwArgs,
    serviceProvider,
)
    args, kwArgs =
        _transform_args_(self, args, kwArgs, dispid, lcid, wFlags, serviceProvider)
    return _invokeex_(DesignatedWrapPolicy, self, dispid, lcid, wFlags, args, kwArgs)
end

mutable struct DynamicPolicy <: AbstractDynamicPolicy
    #= A policy which dynamically (ie, at run-time) determines public interfaces.

        A dynamic policy is used to dynamically dispatch methods and properties to the
        wrapped object.  The list of objects and properties does not need to be known in
        advance, and methods or properties added to the wrapped object after construction
        are also handled.

        The wrapped object must provide the following attributes:

        _dynamic_ -- A method that will be called whenever an invoke on the object
               is called.  The method is called with the name of the underlying method/property
               (ie, the mapping of dispid to/from name has been resolved.)  This name property
               may also be '_value_' to indicate the default, and '_NewEnum' to indicate a new
               enumerator is requested.

         =#
    _next_dynamic_::Int64
    _min_dynamic_::Int64
    _dyn_dispid_to_name_::Dict{Any, String}
    _obj_
    _name_to_dispid_
end
function _wrap_(self::DynamicPolicy, object)
    _wrap_(BasicWrapPolicy, self)
    if !hasfield(typeof(self._obj_), :_dynamic_)
        throw(error("Object does not support Dynamic COM Policy"))
    end
    self._next_dynamic_ = 1000
    self._min_dynamic_ = 1000
    self._dyn_dispid_to_name_ =
        Dict(DISPID_VALUE => "_value_", DISPID_NEWENUM => "_NewEnum")
end

function _getdispid_(self::DynamicPolicy, name, fdex)::Int64
    lname = lower(name)
    try
        return self._name_to_dispid_[lname+1]
    catch exn
        if exn isa KeyError
            dispid = self._next_dynamic_ + 1
            self._next_dynamic_ = self._next_dynamic_ + 1
            self._name_to_dispid_[lname+1] = dispid
            self._dyn_dispid_to_name_[dispid+1] = name
            return dispid
        end
    end
end

function _invoke_(self::DynamicPolicy, dispid, lcid, wFlags, args)
    return (S_OK, -1, _invokeex_(self, dispid, lcid, wFlags, args, nothing, nothing))
end

function _invokeex_(
    self::DynamicPolicy,
    dispid,
    lcid,
    wFlags,
    args,
    kwargs,
    serviceProvider,
)
    try
        name = self._dyn_dispid_to_name_[dispid+1]
    catch exn
        if exn isa KeyError
            throw(COMException(winerror.DISP_E_MEMBERNOTFOUND, "Member not found"))
        end
    end
    return _dynamic_(self._obj_, name, lcid, wFlags, args)
end

DefaultPolicy = DesignatedWrapPolicy
function resolve_func(spec)
    #= Resolve a function by name

        Given a function specified by 'module.function', return a callable object
        (ie, the function itself)
         =#
    try
        idx = rindex(spec, ".")
        mname = spec[begin:idx]
        fname = spec[idx+2:end]
        module_ = _import_module(mname)
        return getfield(module_, :fname)
    catch exn
        if exn isa ValueError
            return globals()[spec+1]
        end
    end
end

function call_func(spec)
    #= Call a function specified by name.

        Call a function specified by 'module.function' and return the result.
         =#
    return resolve_func(spec)(args...)
end

function _import_module(mname)
    #= Import a module just like the 'import' statement.

        Having this function is much nicer for importing arbitrary modules than
        using the 'exec' keyword.  It is more efficient and obvious to the reader.
         =#
    __import__(mname)
    return sys.modules[mname+1]
end

try
    using dispatcher: DispatcherTrace, DispatcherWin32trace
catch exn
    if exn isa ImportError
        #= pass =#
    end
end
