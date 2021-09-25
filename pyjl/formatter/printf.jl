using Base.Ryu

abstract type FmtType end

struct FmtDec <: FmtType end
struct FmtOct <: FmtType end
struct FmtHex <: FmtType end
struct FmtChr <: FmtType end
struct FmtStr <: FmtType end
struct FmtPtr <: FmtType end

struct FmtFltE <: FmtType end
struct FmtFltF <: FmtType end
struct FmtFltG <: FmtType end
struct FmtFltA <: FmtType end

struct FmtN <: FmtType end

const VALID_FMTS = b"duoxefgacsipnDUOXEFGACS"

const FMT_TYPES = [FmtDec, FmtDec, FmtOct, FmtHex, FmtFltE, FmtFltF, FmtFltG, FmtFltA, FmtChr, FmtStr,
                   FmtDec, FmtPtr, FmtN]

# format specifier categories
const FmtInts = Union{FmtDec, FmtOct, FmtHex}
const FmtFlts = Union{FmtFltE, FmtFltF, FmtFltG, FmtFltA}

"""
Typed representation of a format specifier.

Fields are the various modifiers allowed for various format specifiers.
"""
struct FmtSpec{T<:FmtType}
    char::UInt8
    tsep::UInt8 # thousands separator (default ',')
    leftalign::Bool
    plus::Bool
    space::Bool
    zero::Bool
    altf::Bool # alternate formatting ('#' flag)
    width::Int # negative means *, 0 means no width specified
    prec::Int # -2 means *, -1 means no precision specified
end

# recreate the format specifier string from a typed FmtSpec
Base.string(f::FmtSpec; modifier::String="") =
    string("%",
           f.leftalign ? "-" : "",
           f.plus ? "+" : "",
           f.space ? " " : "",
           f.zero ? "0" : "",
           f.altf ? "#" : "",
           f.tsep == 0 ? "" : "'",
           f.width > 0 ? "$(f.width)" : f.width < 0 ? "*" : "",
           f.prec < -1 ? "*" : f.prec >= 0 ? ".$(f.prec)" : "",
           modifier,
           Char(f.char))
Base.show(io::IO, f::FmtSpec) = print(io, string(f))

floatfmt(s::FmtSpec) =
    FmtSpec{FmtFltF}(s.char, s.tsep, s.leftalign, s.plus, s.space, s.zero, s.altf, s.width, 0)
ptrfmt(s::FmtSpec, x) =
    FmtSpec{FmtHex}(s.char, s.tsep, s.leftalign, s.plus, s.space, s.zero, true, s.width,
                    ifelse(sizeof(x) == 8, 16, 8))

function FmtSpec(s::FmtSpec{F}; width=s.width, prec=s.prec) where {F}
    s.width < 0 || throw(ArgumentError("Already has width $(s.width)"))
    s.prec < -1 || throw(ArgumentError("Already has precision $(s.prec)"))
    width < 0 && throw(ArgumentError("Width $(width) must be >= 0"))
    prec < -1 && throw(ArgumentError("Precision $(prec) must be >= -1"))
    FmtSpec{F}(s.char, s.tsep, s.leftalign, s.plus, s.space, s.zero, s.altf, width, prec)
end

# parse format string
function FmtSpec(f::AbstractString)
    isempty(f) && throw(ArgumentError("empty format string"))
    bytes = codeunits(f) # Note: codeunits are not necessarily *bytes*!
    len = length(bytes)
    bytes[1] === UInt8('%') || throw(ArgumentError("Format string doesn't start with %"))
    b = bytes[2]
    pos = 3
    # positioned at start of first format str %
    # parse flags
    leftalign = plus = space = zero = altf = false
    tsep = UInt8(0)
    while true
        if b == UInt8('-')
            leftalign = true
        elseif b == UInt8('+')
            plus = true
        elseif b == UInt8(' ')
            space = true
        elseif b == UInt8('0')
            zero = true
        elseif b == UInt8('#')
            altf = true
        elseif b == UInt8('\'')
            tsep = UInt8(',')
        else
            break
        end
        pos > len && throw(ArgumentError("incomplete format string: '$f'"))
        b = bytes[pos]
        pos += 1
    end
    leftalign && (zero = false)
    # parse width
    if b == UInt('*')
        width = -1
    else
        width = 0
        while b - UInt8('0') < 0x0a
            width = 10 * width + (b - UInt8('0'))
            b = bytes[pos]
            pos += 1
            pos > len && break
        end
    end
    # parse prec
    prec = -1
    parsedprecdigits = false
    if b == UInt8('.')
        pos > len && throw(ArgumentError("incomplete format string: '$f'"))
        parsedprecdigits = true
        b = bytes[pos]
        pos += 1
        if pos <= len
            if b == UInt('*')
                prec == -2
            else
                prec = 0
                while b - UInt8('0') < 0x0a
                    prec = 10 * prec + (b - UInt8('0'))
                    b = bytes[pos]
                    pos += 1
                    pos > len && break
                end
            end
        end
    end
    # parse length modifier (ignored)
    if b == UInt8('h') || b == UInt8('l')
        prev = b
        b = bytes[pos]
        pos += 1
        if b == prev
            pos > len && throw(ArgumentError("invalid format string: '$f'"))
            b = bytes[pos]
            pos += 1
        end
    elseif b in b"Ljqtz"
        b = bytes[pos]
        pos += 1
    end
    # parse type
    fmtind = findfirst(isequal(b), VALID_FMTS)
    fmtind === nothing &&
        throw(ArgumentError(string("invalid format string: '$f', ",
                                   "invalid type specifier: '$(Char(b))'")))
    # Check for uppercase variants
    fmtind > 13 && (fmtind -= 13)
    fmttyp = FMT_TYPES[fmtind]
    if fmttyp <: FmtInts && prec > 0
        zero = false
    elseif !parsedprecdigits
        if (fmttyp === FmtStr || fmttyp === FmtChr || fmttyp === FmtFltA)
            prec = -1
        elseif fmttyp <: FmtFlts
            prec = 6
        end
    end
    FmtSpec{fmttyp}(b, tsep, leftalign, plus, space, zero, altf, width, prec)
end

@inline gethexbase(spec) = spec.char < UInt8('a') ? b"0123456789ABCDEF" : b"0123456789abcdef"

@inline upchar(spec, ch) = (spec.char & 0x20) | UInt8(ch)

# write out a single arg according to format options
# char
@inline function writechar(buf, pos, c::Char)
    u = bswap(reinterpret(UInt32, c))
    while true
        @inbounds buf[pos] = u % UInt8
        pos += 1
        (u >>= 8) == 0 && break
    end
    return pos
end

@inline function padn(buf, pos, cnt)
    @inbounds for _ = 1:cnt
        buf[pos] = UInt8(' ')
        pos += 1
    end
    pos
end

@inline function padzero(buf, pos, cnt)
    @inbounds for _ = 1:cnt
        buf[pos] = UInt8('0')
        pos += 1
    end
    pos
end

function _fmt(buf, pos, spec::FmtSpec{FmtChr}, arg)
    ch = arg isa String ? arg[1] : Char(arg)
    width = spec.width - 1
    width <= 0 && return writechar(buf, pos, ch)
    if spec.leftalign
        padn(buf, writechar(buf, pos, ch), width)
    else
        writechar(buf, padn(buf, pos, width), ch)
    end
end

@inline function outch(buf, pos, ch)
    @inbounds buf[pos] = UInt8(ch)
    pos + 1
end
@inline function outch(buf, pos, c1, c2)
    @inbounds buf[pos] = UInt8(c1)
    @inbounds buf[pos + 1] = UInt8(c2)
    pos + 2
end
@inline function outch(buf, pos, c1, c2, c3)
    @inbounds buf[pos] = UInt8(c1)
    @inbounds buf[pos + 1] = UInt8(c2)
    @inbounds buf[pos + 2] = UInt8(c3)
    pos + 3
end

# strings
function _fmt(buf, pos, spec::FmtSpec{FmtStr}, arg)
    altf, width, prec = spec.altf, spec.width, spec.prec
    str = altf && (arg isa Symbol || arg isa AbstractString) ? repr(arg) : string(arg)
    slen = length(str)
    op = p = prec == -1 ? slen : min(slen, prec)
    # Make sure there is enough room in buffer
    nlen = max(width, p)
    buflen = sizeof(buf) - pos
    buflen < nlen && resize!(buf, nlen + pos)
    !spec.leftalign && width > p && (pos = padn(buf, pos, width - p))
    for c in str
        p == 0 && break
        pos = writechar(buf, pos, c)
        p -= 1
    end
    spec.leftalign && width > op && return padn(buf, pos, width - op)
    return pos
end

const BaseInt = Union{Int8, Int16, Int32, Int64, Int128}
const BaseUns = Union{UInt8, UInt16, UInt32, UInt64, UInt128}

base(::Type{FmtOct}) = 8
base(::Type{FmtDec}) = 10
base(::Type{FmtHex}) = 16

# integers

_fmt(buf, pos, spec::FmtSpec{<:FmtInts}, arg::AbstractFloat) =
    _fmt(buf, pos, floatfmt(spec), arg)

_fmt(buf, pos, spec::FmtSpec{T}, arg::Real) where {T<:FmtInts} =
    _fmt(buf, pos, spec, arg < 0, string(abs(arg); base=base(T)))
_fmt(buf, pos, spec::FmtSpec{<:FmtInts}, arg::BaseUns) =
    _fmt(buf, pos, spec, false, arg)
_fmt(buf, pos, spec::FmtSpec{<:FmtInts}, arg::BaseInt) =
    _fmt(buf, pos, spec, arg < 0, unsigned(abs(arg)))

function _fmt(buf, pos, spec::FmtSpec{F}, neg, x::T) where {F<:FmtInts,T<:Union{String,BaseUns}}
    n = T === String ? sizeof(x) :
        F === FmtDec ? dec_len(x) :
        F === FmtHex ? (sizeof(x)<<1) - (leading_zeros(x)>>2) :
        div((sizeof(x)<<3) - leading_zeros(x)+2, 3)
    i = n
    arglen = n + (neg || (spec.plus | spec.space)) +
        ((spec.altf && (F !== FmtDec)) ? ifelse(F === FmtOct, 1, 2) : 0)
    width, prec = spec.width, spec.prec
    arglen2 = arglen < width && prec > 0 ? arglen + min(max(0, prec - n), width - arglen) : arglen

    # Make sure that remaining output buffer is large enough
    # This means that it isn't necessary to preallocate for cases that usually will never happen
    buflen = sizeof(buf) - pos
    buflen < arglen2 && resize!(buf, arglen2 + pos)

    !spec.leftalign && !spec.zero && arglen2 < width &&
        (pos = padn(buf, pos, width - arglen2))
    if neg
        pos = outch(buf, pos, '-')
    elseif spec.plus # plus overrides space
        pos = outch(buf, pos, '+')
    elseif spec.space
        pos = outch(buf, pos, ' ')
    end
    if spec.altf
        if F === FmtOct
            pos = outch(buf, pos, '0')
        elseif F === FmtHex
            pos = outch(buf, pos, '0', upchar(spec, 'X'))
        end
    end
    if spec.zero && arglen2 < width
        pos = padzero(buf, pos, width - arglen2)
    elseif n < prec
        pos = padzero(buf, pos, prec - n)
    elseif arglen < arglen2
        pos = padzero(buf, pos, arglen2 - arglen)
    end
    if T === String
        GC.@preserve buf x begin
            unsafe_copyto!(pointer(buf, pos), pointer(x), n)
        end
    elseif F === FmtDec
        while i > 0
            d, r = divrem(x, 10)
            @inbounds buf[pos + i - 1] = UInt8('0') + r
            x = oftype(x, d)
            i -= 1
        end
    elseif F === FmtHex
        hexbase = gethexbase(spec)
        while i > 0
            @inbounds buf[pos + i - 1] = hexbase[(x & 0x0f) + 1]
            x >>= 4
            i -= 1
        end
    else # F === FmtOct
        while i > 0
            @inbounds buf[pos + i - 1] = UInt8('0') + (x & 0x07)
            x >>= 3
            i -= 1
        end
    end
    (spec.leftalign && arglen2 < width) ? padn(buf, pos + n, width - arglen2) : (pos + n)
end

# floats
"""
    tofloat(x)

Convert an argument to a Base float type for printf formatting.
By default, arguments are converted to `Float64` via `Float64(x)`.
Custom numeric types that have a conversion to a Base float type
that wish to hook into printf formatting can extend this method like:

```julia
Printf.tofloat(x::MyCustomType) = convert_my_custom_type_to_float(x)
```

For arbitrary precision numerics, you might extend the method like:

```julia
Printf.tofloat(x::MyArbitraryPrecisionType) = BigFloat(x)
```
"""
tofloat(x) = Float64(x)
tofloat(x::Base.IEEEFloat) = x

function output_fmt_a(buf, pos, spec, neg, x)
    if neg
        pos = outch(buf, pos, '-')
    elseif spec.plus
        pos = outch(buf, pos, '+')
    elseif spec.space
        pos = outch(buf, pos, ' ')
    end
    isnan(x) && return outch(buf, pos, 'N', 'a', 'N')
    isfinite(x) || return outch(buf, pos, 'I', 'n', 'f')
    prec = spec.prec
    pos = outch(buf, pos, '0', upchar(spec, 'X'))
    if x == 0
        pos = outch(buf, pos, '0')
        prec > 0 && (pos = padzero(buf, pos, prec))
        return outch(buf, pos, upchar(spec, 'P'), '+', '0')
    end
    s, p = frexp(x)
    prec = spec.prec
    if prec > -1
        sigbits = 4 * min(prec, 13)
        s = 0.25 * round(ldexp(s, 1 + sigbits))
        # ensure last 2 exponent bits either 01 or 10
        u = (reinterpret(UInt64, s) & 0x003f_ffff_ffff_ffff) >> (52 - sigbits)
        i = n = (sizeof(u) << 1) - (leading_zeros(u) >> 2)
    else
        s *= 2.0
        u = (reinterpret(UInt64, s) & 0x001f_ffff_ffff_ffff)
        t = (trailing_zeros(u) >> 2)
        u >>= (t << 2)
        i = n = 14 - t
    end
    frac = u > 9 || spec.altf || prec > 0
    hexbase = gethexbase(spec)
    while i > 1
        buf[pos + i] = hexbase[(u & 0x0f) + 1]
        u >>= 4
        i -= 1
        prec -= 1
    end
    frac && (buf[pos + 1] = UInt8('.'))
    buf[pos] = hexbase[(u & 0x0f) + 1]
    pos += n + frac
    while prec > 0
        pos = outch(buf, pos, '0')
        prec -= 1
    end
    pos = outch(buf, pos, upchar(spec, 'P'))
    p -= 1
    pos = outch(buf, pos, p < 0 ? UInt8('-') : UInt8('+'))
    p = p < 0 ? -p : p
    n = i = ndigits(p, base=10, pad=1)
    while i > 0
        d, r = divrem(p, 10)
        buf[pos + i - 1] = UInt8('0') + r
        p = oftype(p, d)
        i -= 1
    end
    return pos + n
end

const _strspec = Dict{FmtSpec,ASCIIStr}()

"""Get the format specification, prepared for use with MPFR for BigFloats"""
function _get_strspec(spec)
    global _strspec
    chkspec = get(_strspec, spec, nothing)
    chkspec === nothing || return chkspec
    _strspec[spec] = string(spec; modifier="R")
end

@static if VERSION < v"1.5"
_snprintf(ptr, siz, spec, arg) =
    ccall((:mpfr_snprintf,:libmpfr), Int32,
          (Ptr{UInt8}, Culong, Ptr{UInt8}, Ref{BigFloat}...),
          ptr, siz, spec, arg)
else
_snprintf(ptr, siz, spec, arg) =
    @ccall "libmpfr".mpfr_snprintf(ptr::Ptr{UInt8}, siz::Csize_t, spec::Ptr{UInt8};
                                   arg::Ref{BigFloat})::Cint
end

function _fmt(buf, pos, spec::FmtSpec{<:FmtFlts}, arg::BigFloat)
    isfinite(arg) || return _fmt(buf, pos, spec, Float64(arg))
    strspec = _get_strspec(spec)
    siz = length(buf) - pos + 1
    # Calculate size needed for most common outputs
    len = max(spec.width, ceil(Int, precision(arg) * log(2)/log(10)) + 24)
    if len > siz
        resize!(buf, pos + len + 1)
        siz = length(buf) - pos + 1
    end
    GC.@preserve buf begin
        len = _snprintf(pointer(buf, pos), siz, strspec, arg)
        if len > siz
            resize!(buf, pos + len + 1)
            len = _snprintf(pointer(buf, pos), len + 1, strspec, arg)
        end
    end
    len > 0 || error("invalid printf formatting for BigFloat")
    pos + len
end

function _fmt(buf, pos, spec::FmtSpec{T}, arg) where {T <: FmtFlts}
    # Make sure there is enough room
    width = spec.width
    buflen = sizeof(buf) - pos
    needed = max(width, 309 + 17 + 5)
    buflen < needed && resize!(buf, pos + needed)

    x = tofloat(arg)
    if T === FmtFltE
        newpos = Ryu.writeexp(buf, pos, x, spec.prec, spec.plus, spec.space,
                              spec.altf, upchar(spec, 'E'), UInt8('.'))
    elseif T === FmtFltF
        newpos = Ryu.writefixed(buf, pos, x, spec.prec, spec.plus, spec.space, spec.altf,
                                UInt8('.'))
    elseif T === FmtFltG
        prec = spec.prec
        prec = prec == 0 ? 1 : prec
        x = round(x, sigdigits=prec)
        newpos = Ryu.writeshortest(buf, pos, x, spec.plus, spec.space, spec.altf, prec,
                                   upchar(spec, 'E'), true, UInt8('.'))
    elseif T === FmtFltA
        newpos = output_fmt_a(buf, pos, spec, x < 0, abs(x))
    end
    if newpos - pos < width
        # need to pad
        if spec.leftalign
            # easy case, just pad spaces after number
            newpos = padn(buf, newpos, width - (newpos - pos))
        else
            # right aligned
            n = width - (newpos - pos)
            if spec.zero
                ex = (arg < 0 || (spec.plus | spec.space)) + ifelse(T === FmtFltA, 2, 0)
                so = pos + ex
                len = (newpos - pos) - ex
                copyto!(buf, so + n, buf, so, len)
                for i = so:(so + n - 1)
                    buf[i] = UInt8('0')
                end
                newpos += n
            else
                copyto!(buf, pos + n, buf, pos, newpos - pos)
                for i = pos:(pos + n - 1)
                    buf[i] = UInt8(' ')
                end
                newpos += n
            end
        end
    end
    return newpos
end

# pointers
_fmt(buf, pos, spec::FmtSpec{FmtPtr}, arg) =
    _fmt(buf, pos, ptrfmt(spec, arg), UInt(arg))

@inline _dec_len1(v) = ifelse(v < 100, ifelse(v < 10, 1, 2), 3)
@inline _dec_len2(v) = v < 1_000 ? _dec_len1(v) : ifelse(v < 10_000, 4, 5)
@inline _dec_len4(v) = v < 100_000 ? _dec_len2(v) :
    (v < 10_000_000 ? ifelse(v < 1_000_000, 6, 7) : ifelse(v < 100_000_000, 8, 9))
@inline function _dec_len8(v)
    if v < 1_000_000_000 # 1 - 9 digits
        _dec_len4(v)
    elseif v < 10_000_000_000_000 # 10 - 13 digits
        if v < 100_000_000_000
            ifelse(v < 10_000_000_000, 10, 11)
        else
            ifelse(v < 1_000_000_000_000, 12, 13)
        end
    elseif v < 100_000_000_000_000_000 # 14 - 17 digits
        if v < 1_000_000_000_000_000
            ifelse(v < 100_000_000_000_000, 14, 15)
        else
            ifelse(v < 10_000_000_000_000_000, 16, 17)
        end
    else
        v < 10_000_000_000_000_000_000 ? ifelse(v < 1_000_000_000_000_000_000, 18, 19) : 20
    end
end

@inline dec_len(v::UInt8)  = _dec_len1(v)
@inline dec_len(v::UInt16) = _dec_len2(v)
@inline dec_len(v::UInt32) = _dec_len4(v)
@inline dec_len(v::UInt64) = _dec_len8(v)
@inline function dec_len(v::UInt128)
    v <= typemax(UInt64) && return _dec_len8(v%UInt64)
    v = div(v, 0x8ac7230489e80000) # 10^19
    v <= typemax(UInt64) ? _dec_len8(v%UInt64) + 19 : 39
end
