#= General client side utilities.

This module contains utility functions, used primarily by advanced COM
programmers, or other COM modules.
 =#
using PyCall
pythoncom = pyimport("pythoncom")

using win32com_.client: Dispatch, _get_good_object_
abstract type AbstractEnumerator end
abstract type AbstractEnumVARIANT <: AbstractEnumerator end
abstract type AbstractIterator end
PyIDispatchType = pythoncom.TypeIIDs[pythoncom.IID_IDispatch+1]
function WrapEnum(ob, resultCLSID = nothing)::EnumVARIANT
    #= Wrap an object in a VARIANT enumerator.

        All VT_DISPATCHs returned by the enumerator are converted to wrapper objects
        (which may be either a class instance, or a dynamic.Dispatch type object).

         =#
    if type_(ob) != pythoncom.TypeIIDs[pythoncom.IID_IEnumVARIANT+1]
        ob = QueryInterface(ob, pythoncom.IID_IEnumVARIANT)
    end
    return EnumVARIANT(ob, resultCLSID)
end

mutable struct Enumerator <: AbstractEnumerator
    #= A class that provides indexed access into an Enumerator

        By wrapping a PyIEnum* object in this class, you can perform
        natural looping and indexing into the Enumerator.

        Looping is very efficient, but it should be noted that although random
        access is supported, the underlying object is still an enumerator, so
        this will force many reset-and-seek operations to find the requested index.

         =#
    _oleobj_
    index::Int64
    resultCLSID
end
function __getitem__(self::Enumerator, index)
    return __GetIndex(self, index)
end

function __call__(self::Enumerator, index)
    return __GetIndex(self, index)
end

function __GetIndex(self::Enumerator, index)
    if type_(index) != type_(0)
        throw(TypeError("Only integer indexes are supported for enumerators"))
    end
    if index != (self.index + 1)
        Reset(self._oleobj_)
        if index
            Skip(self._oleobj_, index)
        end
    end
    self.index = index
    result = Next(self._oleobj_, 1)
    if length(result) != 0
        return _make_retval_(self, result[1])
    end
    throw(IndexError("list index out of range"))
end

function Next(self::Enumerator, count = 1)::Tuple
    ret = Next(self._oleobj_, count)
    realRets = []
    for r in ret
        push!(realRets, _make_retval_(self, r))
    end
    return tuple(realRets)
end

function Reset(self::Enumerator)
    return Reset(self._oleobj_)
end

function Clone(self::Enumerator)
    return __class__(self, Clone(self._oleobj_), self.resultCLSID)
end

function _make_retval_(self::Enumerator, result)
    return result
end

mutable struct EnumVARIANT <: AbstractEnumVARIANT
    resultCLSID

    EnumVARIANT(enum, resultCLSID = nothing) = begin
        Enumerator(enum)
        new(enum, resultCLSID)
    end
end
function _make_retval_(self::EnumVARIANT, result)
    return _get_good_object_(result, self.resultCLSID)
end

mutable struct Iterator <: AbstractIterator
    resultCLSID
    _iter_
end
function __iter__(self::Iterator)
    return self
end

function __next__(self::Iterator)
    return _get_good_object_(next(self._iter_), self.resultCLSID)
end
