# copied from https://github.com/JuliaLang/julia/pull/30924
# modified to be in compliance with C99: http://port70.net/~nsz/c/c99/n1256.html#6.7.2.2
# Cloned from github on 19/09/2021
# Modified to support StrEnum from Python
module PyEnum

import Core.Intrinsics.bitcast
export @pyenum

function namemap end
function name_value_pairs end

"""
    PyEnum{T<:Any}
The abstract supertype of all enumerated types defined with [`@pyenum`](@ref).
"""
abstract type Pyenum{T<:Any} end

basetype(::Type{<:Pyenum{T}}) where {T<:Any} = T

(::Type{T})(x::Pyenum{T2}) where {T<:Any,T2<:Any} = T(bitcast(T2, x))::T
Base.cconvert(::Type{T}, x::Pyenum{T2}) where {T<:Any,T2<:Any} = T(x)
Base.write(io::IO, x::Pyenum{T}) where {T<:Any} = write(io, T(x))
Base.read(io::IO, ::Type{T}) where {T<:Pyenum} = T(read(io, basetype(T)))

Base.isless(x::T, y::T) where {T<:Pyenum} = isless(basetype(T)(x), basetype(T)(y))

Base.Symbol(x::Pyenum)::Symbol = get(namemap(typeof(x)), x, :UnknownMember)

Base.print(io::IO, x::Pyenum) = print(io, Symbol(x))

function Base.show(io::IO, x::Pyenum)
    sym = Symbol(x)
    if !get(io, :compact, false)
        from = get(io, :module, Main)
        def = typeof(x).name.module
        if from === nothing || !Base.isvisible(sym, def, from)
            show(io, def)
            print(io, ".")
        end
    end
    print(io, sym)
end

function Base.show(io::IO, ::MIME"text/plain", x::Pyenum)
    print(io, x, "::")
    show(IOContext(io, :compact => true), typeof(x))
    print(io, " = ")
    show(io, x)
end

function Base.show(io::IO, ::MIME"text/plain", t::Type{<:Pyenum})
    print(io, "PyEnum ")
    Base.show_datatype(io, t)
    print(io, ":")
    for (s, i) in name_value_pairs(t)
        print(io, "\n", Symbol(s), " = ")
        show(io, i)
    end
end

# give PyEnum types scalar behavior in broadcasting
Base.broadcastable(x::Pyenum) = Ref(x)

@noinline enum_argument_error(typename, x) = throw(ArgumentError(string("input value out of range for PyEnum $(typename): $x")))

macro PyEnum(T, syms...)
    if isempty(syms)
        throw(ArgumentError("no arguments given for PyEnum $T"))
    end
    basetype = Any
    typename = T
    if isa(T, Expr) && T.head == :(::) && length(T.args) == 2 && isa(T.args[1], Symbol)
        typename = T.args[1]
        basetype = Core.eval(__module__, T.args[2])
        if !isa(basetype, DataType) #|| !isbitstype(basetype)
            throw(ArgumentError("invalid base type for PyEnum $typename, $T=::$basetype"))
        end
    elseif !isa(T, Symbol)
        throw(ArgumentError("invalid type expression for PyEnum $T"))
    end
    seen = Set{Symbol}()
    name_values = Tuple{Symbol,basetype}[]
    namemap = Dict{basetype,Symbol}()
    # lo = hi = 0
    i = typemin(basetype) # Changed from zero to typemin

    if length(syms) == 1 && syms[1] isa Expr && syms[1].head == :block
        syms = syms[1].args
    end
    for s in syms
        s isa LineNumberNode && continue
        if isa(s, Symbol)
            # Probably does not work
            if i == typemin(basetype) && !isempty(name_values)
                throw(ArgumentError("overflow in value \"$s\" of PyEnum $typename"))
            end
        elseif isa(s, Expr) &&
               (s.head == :(=) || s.head == :kw) &&
               length(s.args) == 2 && isa(s.args[1], Symbol)
            i = Core.eval(__module__, s.args[2]) # allow exprs, e.g. uint128"1"
            i = convert(basetype, i)
            s = s.args[1]
        else
            throw(ArgumentError(string("invalid argument for PyEnum ", typename, ": ", s)))
        end
        if !Base.isidentifier(s)
            throw(ArgumentError("invalid name for PyEnum $typename; \"$s\" is not a valid identifier"))
        end
        haskey(namemap, i) || (namemap[i] = s;)
        if s in seen
            throw(ArgumentError("name \"$s\" in PyEnum $typename is not unique"))
        end
        push!(seen, s)
        push!(name_values, (s,i))
        # if length(name_values) == 1
        #     lo = hi = i
        # else
        #     lo = min(lo, i)
        #     hi = max(hi, i)
        # end
        # i += oneunit(i)
    end
    blk = quote
        # enum definition
        Base.@__doc__(primitive type $(esc(typename)) <: Pyenum{$(basetype)} $(sizeof(basetype) * 8) end) # "* 8" will probably fail
        function $(esc(typename))(x::Any)
            x ≤ typemax(x) || enum_argument_error($(Expr(:quote, typename)), x)
            return bitcast($(esc(typename)), convert($(basetype), x))
        end
        Pyenum.namemap(::Type{$(esc(typename))}) = $(esc(namemap))
        Pyenum.name_value_pairs(::Type{$(esc(typename))}) = $(esc(name_values))
        # Base.typemin(x::Type{$(esc(typename))}) = $(esc(typename))($lo)
        # Base.typemax(x::Type{$(esc(typename))}) = $(esc(typename))($hi)
        let insts = (Any[ $(esc(typename))(v[2]) for v in $name_values ]...,)
            Base.instances(::Type{$(esc(typename))}) = insts
        end
    end
    if isa(typename, Symbol)
        for (sym, i) in name_values
            push!(blk.args, :(const $(esc(sym)) = $(esc(typename))($i)))
        end
    end
    push!(blk.args, :nothing)
    blk.head = :toplevel
    return blk
end

include("operators.jl")

end # module
