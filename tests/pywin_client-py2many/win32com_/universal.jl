module universal
using PyCall
pythoncom = pyimport("pythoncom")
import win32com.client.build


using win32com.client: gencache
abstract type AbstractArg end
abstract type AbstractMethod end
abstract type AbstractDefinition end
com_error = com_error(pythoncom)
_univgw = _univgw(pythoncom)
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
                if typekind(attr) == TKIND_INTERFACE(pythoncom) ||
                   typekind(attr) == TKIND_DISPATCH(pythoncom) &&
                   wTypeFlags(attr) & TYPEFLAG_FDUAL(pythoncom)
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
            if typekind(attr) == TKIND_DISPATCH(pythoncom)
                refhtype = GetRefTypeOfImplType(type_info, -1)
                type_info = GetRefTypeInfo(type_info, refhtype)
                attr = GetTypeAttr(type_info)
            end
            item = VTableItem(
                win32com.client.build,
                type_info,
                attr,
                GetDocumentation(type_info, -1),
            )
            _doCreateVTable(
                clsid(item),
                python_name(item),
                bIsDispatch(item),
                vtableFuncs(item),
            )
            for info in vtableFuncs(item)
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
                iid = NamesToIIDMap(mod)[name+1]
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
            is_dispatch = getattr(sub_mod, name + "_vtables_dispatch_", nothing)
            method_defs = getattr(sub_mod, name + "_vtables_", nothing)
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
    if t & (VT_BYREF(pythoncom) | VT_ARRAY(pythoncom))
        cb = SizeOfVT(_univgw, VT_PTR(pythoncom))[2]
    elseif t == VT_RECORD(pythoncom)
        cb = SizeOfVT(_univgw, VT_PTR(pythoncom))[2]
    else
        cb = SizeOfVT(_univgw, t)[2]
    end
    return cb
end

mutable struct Arg <: AbstractArg
    name::Any
    offset::Int64
    size::Any

    Arg(name::Any, offset::Int64 = 0, size::Any = _CalcTypeSize(arg_info)) =
        new(name, offset, size)
end

mutable struct Method <: AbstractMethod
    _gw_in_args::Tuple
    _gw_out_args::Tuple
    arg_defs::Any
    args::Vector
    cbArgs::Int64
    dispid::Any
    invkind::Any
    isEventSink::Int64
    name::Any
    names::Any
    ret_def::Any

    Method(
        method_info,
        isEventSink = 0,
        _gw_in_args::Tuple = _GenerateInArgTuple(self),
        _gw_out_args::Tuple = _GenerateOutArgTuple(self),
        arg_defs = desc[3],
        args::Vector = [],
        cbArgs::Int64 = cbArgs,
        dispid = dispid,
        invkind = invkind,
        name = name,
        names = all_names[2:end],
        ret_def = desc[9],
    ) = begin
        if isEventSink && name[begin:2] != "On"
            name = "On%s" % name
        end
        for argDesc in arg_defs
            arg = Arg(argDesc)
            arg.offset = cbArgs
            cbArgs = cbArgs + arg.size
            self.args.append(arg)
        end
        new(
            method_info,
            isEventSink,
            _gw_in_args,
            _gw_out_args,
            arg_defs,
            args,
            cbArgs,
            dispid,
            invkind,
            name,
            names,
            ret_def,
        )
    end
end
function _GenerateInArgTuple(self::Method)::Tuple
    l = []
    for arg in self.args
        if inOut(arg) & PARAMFLAG_FIN(pythoncom) || inOut(arg) == 0
            push!(l, (vt(arg), offset(arg), size(arg)))
        end
    end
    return tuple(l)
end

function _GenerateOutArgTuple(self::Method)::Tuple
    l = []
    for arg in self.args
        if inOut(arg) & PARAMFLAG_FOUT(pythoncom) ||
           inOut(arg) & PARAMFLAG_FRETVAL(pythoncom) ||
           inOut(arg) == 0
            push!(l, (vt(arg), offset(arg), size(arg), clsid(arg)))
        end
    end
    return tuple(l)
end

mutable struct Definition <: AbstractDefinition
    _iid::Any
    _is_dispatch::Any
    _methods::Vector

    Definition(
        iid,
        is_dispatch,
        method_defs,
        _iid = iid,
        _is_dispatch = is_dispatch,
        _methods::Vector = [],
    ) = begin
        for info in method_defs
            entry = Method(info)
            self._methods.append(entry)
        end
        new(iid, is_dispatch, method_defs, _iid, _is_dispatch, _methods)
    end
end
function iid(self::Definition)::Definition
    return self._iid
end

function vtbl_argsizes(self::Definition)
    return [cbArgs(m) for m in self._methods]
end

function vtbl_argcounts(self::Definition)
    return [length(args(m)) for m in self._methods]
end

function dispatch(
    self::Definition,
    ob,
    index,
    argPtr,
    ReadFromInTuple = ReadFromInTuple(_univgw),
    WriteFromOutTuple = WriteFromOutTuple(_univgw),
)::Int64
    #= Dispatch a call to an interface method. =#
    meth = self._methods[index+1]
    hr = 0
    args = ReadFromInTuple(_gw_in_args(meth), argPtr)
    ob = getattr(ob, "policy", ob)
    _dispid_to_func_(ob)[dispid(meth)+1] = name(meth)
    retVal = _InvokeEx_(ob, dispid(meth), 0, invkind(meth), args, nothing, nothing)
    if type_(retVal) == tuple
        if length(retVal) == (length(_gw_out_args(meth)) + 1)
            hr = retVal[1]
            retVal = retVal[2:end]
        else
            throw(
                TypeError(
                    "Expected %s return values, got: %s" %
                    (length(_gw_out_args(meth)) + 1, length(retVal)),
                ),
            )
        end
    else
        retVal = [retVal]
        append!(retVal, repeat([nothing], (length(_gw_out_args(meth)) - 1)))
        retVal = tuple(retVal)
    end
    WriteFromOutTuple(retVal, _gw_out_args(meth), argPtr)
    return hr
end

end
