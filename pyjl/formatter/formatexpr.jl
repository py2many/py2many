# formatting expression

### Argument specification

struct ArgSpec
    argidx::Int
    hasfilter::Bool
    filter::Function

    function ArgSpec(idx::Int, hasfil::Bool, filter::Function)
        idx != 0 || error("Argument index cannot be zero.")
        new(idx, hasfil, filter)
    end
end

getarg(args, sp::ArgSpec) =
    (a = args[sp.argidx]; sp.hasfilter ? sp.filter(a) : a)

# pos > 0: must not have iarg in expression (use pos+1), return (entry, pos + 1)
# pos < 0: must have iarg in expression, return (entry, -1)
# pos = 0: no positional argument before, can be either, return (entry, 1) or (entry, -1)
function make_argspec(s::AbstractString, pos::Int)
    # for argument position
    iarg::Int = -1
    hasfil::Bool = false
    ff::Function = Base.identity

    if !isempty(s)
        filrange = findfirst("|>", s)
        if filrange === nothing
            iarg = parse(Int, s)
        else
            ifil = first(filrange)
            iarg = ifil > 1 ? parse(Int, s[1:prevind(s, ifil)]) : -1
            hasfil = true
            ff = m_eval(Symbol(s[ifil+2:end]))
        end
    end

    if pos > 0
        iarg < 0 || error("entry with and without argument index must not coexist.")
        iarg = (pos += 1)
    elseif pos < 0
        iarg > 0 || error("entry with and without argument index must not coexist.")
    else # pos == 0
        if iarg < 0
            iarg = pos = 1
        else
            pos = -1
        end
    end

    return (ArgSpec(iarg, hasfil, ff), pos)
end


### Format entry

struct FormatEntry
    argspec::ArgSpec
    spec::FormatSpec
end

function make_formatentry(s::AbstractString, pos::Int)
    @assert s[1] == '{' && s[end] == '}'
    sc = s[2:prevind(s, lastindex(s))]
    icolon = findfirst(isequal(':'), sc)
    if icolon === nothing  # no colon
        (argspec, pos) = make_argspec(sc, pos)
        spec = FormatSpec('s')
    else
        (argspec, pos) = make_argspec(sc[1:prevind(sc, icolon)], pos)
        spec = FormatSpec(sc[nextind(sc, icolon):end])
    end
    return (FormatEntry(argspec, spec), pos)
end


### Format expression

mutable struct FormatExpr
    prefix::UTF8Str
    suffix::UTF8Str
    entries::Vector{FormatEntry}
    inter::Vector{UTF8Str}
end

_raise_unmatched_lbrace() = error("Unmatched { in format expression.")

function find_next_entry_open(s::AbstractString, si::Int)
    slen = lastindex(s)
    p = findnext(isequal('{'), s, si)
    (p === nothing || p < slen) || _raise_unmatched_lbrace()
    while p !== nothing && s[p+1] == '{'  # escape `{{`
        p = findnext(isequal('{'), s, p+2)
        (p === nothing || p < slen) || _raise_unmatched_lbrace()
    end
    pre = p !== nothing ? s[si:prevind(s, p)] : s[si:end]
    if !isempty(pre)
        pre = replace(pre, "{{" => '{')
        pre = replace(pre, "}}" => '}')
    end
    return (p, convert(UTF8Str, pre))
end

function find_next_entry_close(s::AbstractString, si::Int)
    p = findnext(isequal('}'), s, si)
    p !== nothing || _raise_unmatched_lbrace()
    return p
end

function FormatExpr(s::AbstractString)
    slen = length(s)

    # init
    prefix = UTF8Str("")
    suffix = UTF8Str("")
    entries = FormatEntry[]
    inter = UTF8Str[]

    # scan
    (p, prefix) = find_next_entry_open(s, 1)
    if p !== nothing
        q = find_next_entry_close(s, p+1)
        (e, pos) = make_formatentry(s[p:q], 0)
        push!(entries, e)
        (p, pre) = find_next_entry_open(s, q+1)
        while p !== nothing
            push!(inter, pre)
            q = find_next_entry_close(s, p+1)
            (e, pos) = make_formatentry(s[p:q], pos)
            push!(entries, e)
            (p, pre) = find_next_entry_open(s, q+1)
        end
        suffix = pre
    end
    FormatExpr(prefix, suffix, entries, inter)
end

function printfmt(io::IO, fe::FormatExpr, args...)
    isempty(fe.prefix) || print(io, fe.prefix)
    ents = fe.entries
    ne = length(ents)
    if ne > 0
        e = ents[1]
        printfmt(io, e.spec, getarg(args, e.argspec))
        for i = 2:ne
            print(io, fe.inter[i-1])
            e = ents[i]
            printfmt(io, e.spec, getarg(args, e.argspec))
        end
    end
    isempty(fe.suffix) || print(io, fe.suffix)
end

const StringOrFE = Union{AbstractString, FormatExpr}
printfmt(io::IO, fe::AbstractString, args...) = printfmt(io, FormatExpr(fe), args...)
printfmt(fe::StringOrFE, args...) = printfmt(_stdout(), fe, args...)

printfmtln(io::IO, fe::StringOrFE, args...) = (printfmt(io, fe, args...); println(io))
printfmtln(fe::StringOrFE, args...) = printfmtln(_stdout(), fe, args...)

format(fe::StringOrFE, args...) = sprint(printfmt, fe, args...)
