using PyCall
pythoncom = pyimport("pythoncom")
import win32com_.client.build

using win32com_.client: gencache
abstract type AbstractArg end
abstract type AbstractMethod end
abstract type AbstractDefinition end
com_error = pythoncom.com_error
_univgw = pythoncom._univgw
function RegisterInterfaces(
    typelibGUID,
    lcid,
    major,
    minor,
    interface_names = nothing,
)::Vector
    ret = []
    try
        mod = GetModuleForTypelib(gencache, typelibGUID, lcid, major, minor)
    catch exn
        if exn isa ImportError
            mod = nothing
        end
    end
    if mod === nothing
        tlb = LoadRegTypeLib(pythoncom, typelibGUID, major, minor, lcid)
        typecomp_lib = GetTypeComp(tlb)
        if interface_names === nothing
            interface_names = []
            for i = 0:GetTypeInfoCount(tlb)-1
                info = GetTypeInfo(tlb, i)
                doc = GetDocumentation(tlb, i)
                attr = GetTypeAttr(info)
                if attr.typekind == pythoncom.TKIND_INTERFACE ||
                   attr.typekind == pythoncom.TKIND_DISPATCH &&
                   attr.wTypeFlags & pythoncom.TYPEFLAG_FDUAL
                    push!(interface_names, doc[1])
                end
            end
        end
        for name in interface_names
            type_info, type_comp = BindType(typecomp_lib, name)
            if type_info === nothing
                throw(ValueError("The interface \'%s\' can not be located" % (name,)))
            end
            attr = GetTypeAttr(type_info)
            if attr.typekind == pythoncom.TKIND_DISPATCH
                refhtype = GetRefTypeOfImplType(type_info, -1)
                type_info = GetRefTypeInfo(type_info, refhtype)
                attr = GetTypeAttr(type_info)
            end
            item = VTableItem(
                win32com_.client.build,
                type_info,
                attr,
                GetDocumentation(type_info, -1),
            )
            _doCreateVTable(
                item.clsid,
                item.python_name,
                item.bIsDispatch,
                item.vtableFuncs,
            )
            for info in item.vtableFuncs
                names, dispid, desc = info
                invkind = desc[5]
                push!(ret, (dispid, invkind, names[1]))
            end
        end
    else
        if !(interface_names)
            interface_names = collect(values(mod.VTablesToClassMap))
        end
        for name in interface_names
            try
                iid = mod.NamesToIIDMap[name+1]
            catch exn
                if exn isa KeyError
                    throw(
                        ValueError(
                            "Interface \'%s\' does not exist in this cached typelib" %
                            (name,),
                        ),
                    )
                end
            end
            sub_mod = GetModuleForCLSID(gencache, iid)
            is_dispatch = (
                hasfield(typeof(sub_mod), :name + _vtables_dispatch_) ?
                getfield(sub_mod, :name + _vtables_dispatch_) : nothing
            )
            method_defs = (
                hasfield(typeof(sub_mod), :name + _vtables_) ?
                getfield(sub_mod, :name + _vtables_) : nothing
            )
            if is_dispatch === nothing || method_defs === nothing
                throw(ValueError("Interface \'%s\' is IDispatch only" % (name,)))
            end
            _doCreateVTable(iid, name, is_dispatch, method_defs)
            for info in method_defs
                names, dispid, desc = info
                invkind = desc[5]
                push!(ret, (dispid, invkind, names[1]))
            end
        end
    end
    return ret
end

function _doCreateVTable(iid, interface_name, is_dispatch, method_defs)
    defn = Definition(iid, is_dispatch, method_defs)
    vtbl = CreateVTable(_univgw, defn, is_dispatch)
    RegisterVTable(_univgw, vtbl, iid, interface_name)
end

function _CalcTypeSize(typeTuple)
    t = typeTuple[1]
    if t & (pythoncom.VT_BYREF | pythoncom.VT_ARRAY)
        cb = SizeOfVT(_univgw, pythoncom.VT_PTR)[2]
    elseif t == pythoncom.VT_RECORD
        cb = SizeOfVT(_univgw, pythoncom.VT_PTR)[2]
    else
        cb = SizeOfVT(_univgw, t)[2]
    end
    return cb
end

mutable struct Arg <: AbstractArg
    name
    size
    offset::Int64
end

mutable struct Method <: AbstractMethod
    _gw_in_args
    _gw_out_args
    args::Vector
    cbArgs::Int64
    dispid
    invkind
    name
    isEventSink::Int64

    Method(method_info, isEventSink = 0) = begin
        if isEventSink && name[begin:2] != "On"
            name = "On%s" % name
        end
        for argDesc in arg_defs
            arg = Arg(argDesc)
            arg.offset = cbArgs
            cbArgs = cbArgs + arg.size
            args.append(arg)
        end
        new(method_info, isEventSink)
    end
end
function _GenerateInArgTuple(self::Method)::Tuple
    l = []
    for arg in self.args
        if arg.inOut & pythoncom.PARAMFLAG_FIN || arg.inOut == 0
            push!(l, (arg.vt, arg.offset, arg.size))
        end
    end
    return tuple(l)
end

function _GenerateOutArgTuple(self::Method)::Tuple
    l = []
    for arg in self.args
        if arg.inOut & pythoncom.PARAMFLAG_FOUT ||
           arg.inOut & pythoncom.PARAMFLAG_FRETVAL ||
           arg.inOut == 0
            push!(l, (arg.vt, arg.offset, arg.size, arg.clsid))
        end
    end
    return tuple(l)
end

mutable struct Definition <: AbstractDefinition
    _iid
    _methods::Vector
    _is_dispatch

    Definition(iid, is_dispatch, method_defs) = begin
        for info in method_defs
            entry = Method(info)
            _methods.append(entry)
        end
        new(iid, is_dispatch, method_defs)
    end
end
function iid(self::Definition)
    return self._iid
end

function vtbl_argsizes(self::Definition)
    return [m.cbArgs for m in self._methods]
end

function vtbl_argcounts(self::Definition)
    return [length(m.args) for m in self._methods]
end

function dispatch(
    self::Definition,
    ob,
    index,
    argPtr,
    ReadFromInTuple = _univgw.ReadFromInTuple,
    WriteFromOutTuple = _univgw.WriteFromOutTuple,
)::Int64
    #= Dispatch a call to an interface method. =#
    meth = self._methods[index+1]
    hr = 0
    args = ReadFromInTuple(meth._gw_in_args, argPtr)
    ob = (hasfield(typeof(ob), :policy) ? getfield(ob, :policy) : ob)
    ob._dispid_to_func_[meth.dispid+1] = meth.name
    retVal = _InvokeEx_(ob, meth.dispid, 0, meth.invkind, args, nothing, nothing)
    if type_(retVal) == tuple
        if length(retVal) == (length(meth._gw_out_args) + 1)
            hr = retVal[1]
            retVal = retVal[2:end]
        else
            throw(
                TypeError(
                    "Expected %s return values, got: %s" %
                    (length(meth._gw_out_args) + 1, length(retVal)),
                ),
            )
        end
    else
        retVal = [retVal]
        append!(retVal, repeat([nothing], (length(meth._gw_out_args) - 1)))
        retVal = tuple(retVal)
    end
    WriteFromOutTuple(retVal, meth._gw_out_args, argPtr)
    return hr
end
