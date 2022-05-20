#= Dispatcher

Please see policy.py for a discussion on dispatchers and policies
 =#
using PyCall
win32api = pyimport("win32api")
pythoncom = pyimport("pythoncom")
import win32traceutil

using win32com_.server.exception: IsCOMServerException
using win32com_.util: IIDToInterfaceName
import win32com_
mutable struct DispatcherBase <: AbstractDispatcherBase
    #= The base class for all Dispatchers.

        This dispatcher supports wrapping all operations in exception handlers,
        and all the necessary delegation to the policy.

        This base class supports the printing of "unexpected" exceptions.  Note, however,
        that exactly where the output of print goes may not be useful!  A derived class may
        provide additional semantics for this.
         =#
    policy
    logger
end
function _CreateInstance_(self::DispatcherBase, clsid, reqIID)
    try
        _CreateInstance_(self.policy, clsid, reqIID)
        return WrapObject(pythoncom, self, reqIID)
    catch exn
        return _HandleException_(self)
    end
end

function _QueryInterface_(self::DispatcherBase, iid)
    try
        return _QueryInterface_(self.policy, iid)
    catch exn
        return _HandleException_(self)
    end
end

function _Invoke_(self::DispatcherBase, dispid, lcid, wFlags, args)
    try
        return _Invoke_(self.policy, dispid, lcid, wFlags, args)
    catch exn
        return _HandleException_(self)
    end
end

function _GetIDsOfNames_(self::DispatcherBase, names, lcid)
    try
        return _GetIDsOfNames_(self.policy, names, lcid)
    catch exn
        return _HandleException_(self)
    end
end

function _GetTypeInfo_(self::DispatcherBase, index, lcid)
    try
        return _GetTypeInfo_(self.policy, index, lcid)
    catch exn
        return _HandleException_(self)
    end
end

function _GetTypeInfoCount_(self::DispatcherBase)
    try
        return _GetTypeInfoCount_(self.policy)
    catch exn
        return _HandleException_(self)
    end
end

function _GetDispID_(self::DispatcherBase, name, fdex)
    try
        return _GetDispID_(self.policy, name, fdex)
    catch exn
        return _HandleException_(self)
    end
end

function _InvokeEx_(
    self::DispatcherBase,
    dispid,
    lcid,
    wFlags,
    args,
    kwargs,
    serviceProvider,
)
    try
        return _InvokeEx_(self.policy, dispid, lcid, wFlags, args, kwargs, serviceProvider)
    catch exn
        return _HandleException_(self)
    end
end

function _DeleteMemberByName_(self::DispatcherBase, name, fdex)
    try
        return _DeleteMemberByName_(self.policy, name, fdex)
    catch exn
        return _HandleException_(self)
    end
end

function _DeleteMemberByDispID_(self::DispatcherBase, id)
    try
        return _DeleteMemberByDispID_(self.policy, id)
    catch exn
        return _HandleException_(self)
    end
end

function _GetMemberProperties_(self::DispatcherBase, id, fdex)
    try
        return _GetMemberProperties_(self.policy, id, fdex)
    catch exn
        return _HandleException_(self)
    end
end

function _GetMemberName_(self::DispatcherBase, dispid)
    try
        return _GetMemberName_(self.policy, dispid)
    catch exn
        return _HandleException_(self)
    end
end

function _GetNextDispID_(self::DispatcherBase, fdex, flags)
    try
        return _GetNextDispID_(self.policy, fdex, flags)
    catch exn
        return _HandleException_(self)
    end
end

function _GetNameSpaceParent_(self::DispatcherBase)
    try
        return _GetNameSpaceParent_(self.policy)
    catch exn
        return _HandleException_(self)
    end
end

function _HandleException_(self::DispatcherBase)
    #= Called whenever an exception is raised.

            Default behaviour is to print the exception.
             =#
    if !IsCOMServerException()
        if self.logger != nothing
            exception(self.logger, "pythoncom server error")
        else
            current_exceptions() != [] ? current_exceptions()[end] : nothing
        end
    end
    error()
end

function _trace_(self::DispatcherBase)
    if self.logger != nothing
        record = join(map(str, args), " ")
        debug(self.logger, record)
    else
        for arg in args[begin:-1]
            print("$(arg)")
        end
        println(args[end])
    end
end

abstract type AbstractDispatcherBase end
abstract type AbstractDispatcherTrace <: AbstractDispatcherBase end
abstract type AbstractDispatcherWin32trace <: AbstractDispatcherTrace end
abstract type AbstractDispatcherOutputDebugString <: AbstractDispatcherTrace end
abstract type AbstractDispatcherWin32dbg <: AbstractDispatcherBase end
mutable struct DispatcherTrace <: AbstractDispatcherTrace
    #= A dispatcher, which causes a 'print' line for each COM function called. =#
    policy
end
function _QueryInterface_(self::DispatcherTrace, iid)
    rc = _QueryInterface_(DispatcherBase, self)
    if !(rc)
        _trace_(
            self,
            "in %s._QueryInterface_ with unsupported IID %s (%s)" %
            (repr(self.policy._obj_), IIDToInterfaceName(iid), iid),
        )
    end
    return rc
end

function _GetIDsOfNames_(self::DispatcherTrace, names, lcid)
    _trace_(self, "in _GetIDsOfNames_ with \'%s\' and \'%d\'\n" % (names, lcid))
    return _GetIDsOfNames_(DispatcherBase, self, names)
end

function _GetTypeInfo_(self::DispatcherTrace, index, lcid)
    _trace_(self, "in _GetTypeInfo_ with index=%d, lcid=%d\n" % (index, lcid))
    return _GetTypeInfo_(DispatcherBase, self, index)
end

function _GetTypeInfoCount_(self::DispatcherTrace)
    _trace_(self, "in _GetTypeInfoCount_\n")
    return _GetTypeInfoCount_(DispatcherBase)
end

function _Invoke_(self::DispatcherTrace, dispid, lcid, wFlags, args)
    _trace_(self, "in _Invoke_ with", dispid, lcid, wFlags, args)
    return _Invoke_(DispatcherBase, self, dispid, lcid, wFlags)
end

function _GetDispID_(self::DispatcherTrace, name, fdex)
    _trace_(self, "in _GetDispID_ with", name, fdex)
    return _GetDispID_(DispatcherBase, self, name)
end

function _InvokeEx_(
    self::DispatcherTrace,
    dispid,
    lcid,
    wFlags,
    args,
    kwargs,
    serviceProvider,
)
    _trace_(
        self,
        "in %r._InvokeEx_-%s%r [%x,%s,%r]" %
        (self.policy._obj_, dispid, args, wFlags, lcid, serviceProvider),
    )
    return _InvokeEx_(DispatcherBase, self, dispid, lcid, wFlags, args, kwargs)
end

function _DeleteMemberByName_(self::DispatcherTrace, name, fdex)
    _trace_(self, "in _DeleteMemberByName_ with", name, fdex)
    return _DeleteMemberByName_(DispatcherBase, self, name)
end

function _DeleteMemberByDispID_(self::DispatcherTrace, id)
    _trace_(self, "in _DeleteMemberByDispID_ with", id)
    return _DeleteMemberByDispID_(DispatcherBase, self)
end

function _GetMemberProperties_(self::DispatcherTrace, id, fdex)
    _trace_(self, "in _GetMemberProperties_ with", id, fdex)
    return _GetMemberProperties_(DispatcherBase, self, id)
end

function _GetMemberName_(self::DispatcherTrace, dispid)
    _trace_(self, "in _GetMemberName_ with", dispid)
    return _GetMemberName_(DispatcherBase, self)
end

function _GetNextDispID_(self::DispatcherTrace, fdex, flags)
    _trace_(self, "in _GetNextDispID_ with", fdex, flags)
    return _GetNextDispID_(DispatcherBase, self, fdex)
end

function _GetNameSpaceParent_(self::DispatcherTrace)
    _trace_(self, "in _GetNameSpaceParent_")
    return _GetNameSpaceParent_(DispatcherBase)
end

mutable struct DispatcherWin32trace <: AbstractDispatcherWin32trace
    #= A tracing dispatcher that sends its output to the win32trace remote collector. =#

    DispatcherWin32trace(policyClass, object) = begin
        DispatcherTrace(policyClass, object)
        if logger === nothing
        end
        _trace_("Object with win32trace dispatcher created (object=%s)" % repr(object))
        new(policyClass, object)
    end
end

mutable struct DispatcherOutputDebugString <: AbstractDispatcherOutputDebugString
    #= A tracing dispatcher that sends its output to win32api.OutputDebugString =#

end
function _trace_(self::DispatcherOutputDebugString)
    for arg in args[begin:-1]
        OutputDebugString(win32api, string(arg) * " ")
    end
    OutputDebugString(win32api, string(args[end]) * "\n")
end

mutable struct DispatcherWin32dbg <: AbstractDispatcherWin32dbg
    #= A source-level debugger dispatcher

        A dispatcher which invokes the debugger as an object is instantiated, or
        when an unexpected exception occurs.

        Requires Pythonwin.
         =#

    DispatcherWin32dbg(policyClass, ob) = begin
        win32com_.gen_py.debugger.brk()
        println("The DispatcherWin32dbg dispatcher is deprecated!")
        println("Please let me know if this is a problem.")
        println("Uncomment the relevant lines in dispatcher.py to re-enable")
        DispatcherBase(policyClass, ob)
        new(policyClass, ob)
    end
end
function _HandleException_(self::DispatcherWin32dbg)
    #= Invoke the debugger post mortem capability =#
    typ, val, tb = exc_info()
    debug = 0
    try
        throw(typ(val))
    catch exn
        if exn isa Exception
            debug = get_option(
                GetDebugger(win32com_.gen_py.debugger),
                win32com_.gen_py.debugger.dbgcon.OPT_STOP_EXCEPTIONS,
            )
        end
        debug = 1
    end
    if debug != 0
        try
            post_mortem(win32com_.gen_py.debugger, tb, typ, val)
        catch exn
            current_exceptions() != [] ? current_exceptions()[end] : nothing
        end
    end
    #Delete Unsupported
    del(tb)
    error()
end

try
    import win32trace
    DefaultDebugDispatcher = DispatcherWin32trace
catch exn
    if exn isa ImportError
        DefaultDebugDispatcher = DispatcherTrace
    end
end
