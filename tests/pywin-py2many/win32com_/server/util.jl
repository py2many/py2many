#=  General Server side utilities 
 =#
using PyCall
pythoncom = pyimport("pythoncom")
import win32com_.server.dispatcher

include("policy.jl")
import winerror
using exception: COMException
abstract type AbstractListEnumerator end
abstract type AbstractListEnumeratorGateway <: AbstractListEnumerator end
abstract type AbstractCollection end
abstract type AbstractFileStream end
function wrap(ob, iid = nothing, usePolicy = nothing, useDispatcher = nothing)
    #= Wraps an object in a PyGDispatch gateway.

        Returns a client side PyI{iid} interface.

        Interface and gateway support must exist for the specified IID, as
        the QueryInterface() method is used.

         =#
    if usePolicy === nothing
        usePolicy = policy.DefaultPolicy
    end
    if useDispatcher == 1
        useDispatcher = win32com_.server.dispatcher.DefaultDebugDispatcher
    end
    if useDispatcher === nothing || useDispatcher == 0
        ob = usePolicy(ob)
    else
        ob = useDispatcher(usePolicy, ob)
    end
    ob = WrapObject(pythoncom, ob)
    if iid != nothing
        ob = QueryInterface(ob, iid)
    end
    return ob
end

function unwrap(ob)
    #= Unwraps an interface.

        Given an interface which wraps up a Gateway, return the object behind
        the gateway.
         =#
    ob = UnwrapObject(pythoncom, ob)
    if hasfield(typeof(ob), :policy)
        ob = ob.policy
    end
    return ob._obj_
end

mutable struct ListEnumerator <: AbstractListEnumerator
    #= A class to expose a Python sequence as an EnumVARIANT.

        Create an instance of this class passing a sequence (list, tuple, or
        any sequence protocol supporting object) and it will automatically
        support the EnumVARIANT interface for the object.

        See also the @NewEnum@ function, which can be used to turn the
        instance into an actual COM server.
         =#
    _iid_
    _list_
    index
    _public_methods_::Vector{String}
    iid

    ListEnumerator(
        _iid_,
        _list_,
        index,
        _public_methods_::Vector{String} = ["Next", "Skip", "Reset", "Clone"],
        iid = pythoncom.IID_IEnumVARIANT,
    ) = new(_iid_, _list_, index, _public_methods_, iid)
end
function _query_interface_(self::ListEnumerator, iid)::Int64
    if iid == self._iid_
        return 1
    end
end

function Next(self::ListEnumerator, count)
    result = self._list_[self.index+1:self.index+count]
    Skip(self, count)
    return result
end

function Skip(self::ListEnumerator, count)
    end_ = self.index + count
    if end_ > length(self._list_)
        end_ = length(self._list_)
    end
    self.index = end_
end

function Reset(self::ListEnumerator)
    self.index = 0
end

function Clone(self::ListEnumerator)
    return _wrap(self, __class__(self, self._list_, self.index))
end

function _wrap(self::ListEnumerator, ob)
    return wrap(ob)
end

mutable struct ListEnumeratorGateway <: AbstractListEnumeratorGateway
    #= A List Enumerator which wraps a sequence's items in gateways.

        If a sequence contains items (objects) that have not been wrapped for
        return through the COM layers, then a ListEnumeratorGateway can be
        used to wrap those items before returning them (from the Next() method).

        See also the @ListEnumerator@ class and the @NewEnum@ function.
         =#
    _wrap
end
function Next(self::ListEnumeratorGateway, count)
    result = self._list_[self.index+1:self.index+count]
    Skip(self, count)
    return map(self._wrap, result)
end

function NewEnum(
    seq,
    cls = ListEnumerator,
    iid = pythoncom.IID_IEnumVARIANT,
    usePolicy = nothing,
    useDispatcher = nothing,
)
    #= Creates a new enumerator COM server.

        This function creates a new COM Server that implements the
        IID_IEnumVARIANT interface.

        A COM server that can enumerate the passed in sequence will be
        created, then wrapped up for return through the COM framework.
        Optionally, a custom COM server for enumeration can be passed
        (the default is @ListEnumerator@), and the specific IEnum
        interface can be specified.
         =#
    ob = cls(seq, iid)
    return wrap(ob, iid)
end

mutable struct Collection <: AbstractCollection
    #= A collection of VARIANT values. =#
    _public_methods_::Vector{String}
    data
    _value_
    readOnly::Int64

    Collection(data = nothing, readOnly = 0, _value_ = Item) = begin
        if data === nothing
            data = []
        end
        if readOnly
            _public_methods_ = ["Item", "Count"]
        end
        new(data, readOnly, _value_)
    end
end
function Item(self::Collection)
    if length(args) != 1
        throw(COMException(winerror.DISP_E_BADPARAMCOUNT))
    end
    try
        return self.data[args[1]+1]
    catch exn
        let desc = exn
            if desc isa IndexError
                throw(COMException(winerror.DISP_E_BADINDEX, string(desc)))
            end
        end
    end
end

function Count(self::Collection)::Int64
    return length(self.data)
end

function Add(self::Collection, value)
    append(self.data, value)
end

function Remove(self::Collection, index)
    try
        #Delete Unsupported
        del(self.data)
    catch exn
        let desc = exn
            if desc isa IndexError
                throw(COMException(winerror.DISP_E_BADINDEX, string(desc)))
            end
        end
    end
end

function Insert(self::Collection, index, value)
    try
        index = parse(Int, index)
    catch exn
        if exn isa (ValueError, TypeError)
            throw(COMException(winerror.DISP_E_TYPEMISMATCH))
        end
    end
    insert(self.data, index, value)
end

function _NewEnum(self::Collection)
    return NewEnum(self.data)
end

function NewCollection(seq, cls = Collection)
    #= Creates a new COM collection object

        This function creates a new COM Server that implements the
        common collection protocols, including enumeration. (_NewEnum)

        A COM server that can enumerate the passed in sequence will be
        created, then wrapped up for return through the COM framework.
        Optionally, a custom COM server for enumeration can be passed
        (the default is @Collection@).
         =#
    return WrapObject(
        pythoncom,
        DefaultPolicy(policy, cls(seq)),
        pythoncom.IID_IDispatch,
        pythoncom.IID_IDispatch,
    )
end

mutable struct FileStream <: AbstractFileStream
    file
    _com_interfaces_::Vector
    _public_methods_::Vector{String}

    FileStream(
        file,
        _com_interfaces_::Vector = [pythoncom.IID_IStream],
        _public_methods_::Vector{String} = ["Read", "Write", "Clone", "CopyTo", "Seek"],
    ) = new(file, _com_interfaces_, _public_methods_)
end
function Read(self::FileStream, amount)
    return read(self.file, amount)
end

function Write(self::FileStream, data)::Int64
    write(self.file, data)
    return length(data)
end

function Clone(self::FileStream)
    return _wrap(self, __class__(self, self.file))
end

function CopyTo(self::FileStream, dest, cb)
    data = read(self.file, cb)
    cbread = length(data)
    Write(dest, data)
    return (cbread, cbread)
end

function Seek(self::FileStream, offset, origin)
    seek(self.file, offset, origin)
    return tell(self.file)
end

function _wrap(self::FileStream, ob)
    return wrap(ob)
end
