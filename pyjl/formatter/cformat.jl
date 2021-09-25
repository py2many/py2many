include("printf.jl")

const _formatters = Dict{ASCIIStr,FmtSpec}()

function _get_formatter(fmt)
    global _formatters

    chkfmt = get(_formatters, fmt, nothing)
    chkfmt === nothing || return chkfmt
    _formatters[fmt] = FmtSpec(fmt)
end

_cfmt_comma(fspec::FmtSpec, x) = addcommasreal(_cfmt(fspec, x))
_cfmt_comma(fspec::FmtSpec{FmtStr}, x::Rational) =  addcommasrat(_cfmt(fspec, x))
_cfmt_comma(fspec::FmtSpec{<:FmtInts}, x) = checkcommas(_cfmt(fspec, x))

function _cfmt(fspec::FmtSpec, x)
    sv = Base.StringVector(23) # Trust that lower level code will expand if necessary
    pos = _fmt(sv, 1, fspec, x)
    resize!(sv, pos - 1)
    String(sv)
end

cfmt(fspec::FmtSpec, x) = fspec.tsep == 0 ? _cfmt(fspec, x) : _cfmt_comma(fspec, x)
cfmt(fmtstr::ASCIIStr, x) = cfmt(_get_formatter(fmtstr), x)

function generate_formatter(fmt::ASCIIStr)
    fspec = _get_formatter(fmt)
    fspec.tsep == 0 ? x -> _cfmt(fspec, x) : x -> _cfmt_comma(fspec, x)
end

function addcommasreal(s)
    len = length(s)
    dpos = findfirst( isequal('.'), s )
    dpos !== nothing && return addcommas(s, len, dpos-1)
    # find the rightmost digit
    for i in len:-1:1
        isdigit( s[i] ) && return addcommas(s, len, i)
    end
    s
end

# commas are added to only the numerator
addcommasrat(s) = addcommas(s, length(s), findfirst( isequal('/'), s )-1)

function checkcommas(s)
    len = length(s)
    for i in len:-1:1
        isdigit( s[i] ) && return addcommas(s, len, i)
    end
    s
end

function addcommas(s::T, len, lst) where {T<:AbstractString}
    lst < 4 && return s
    beg = 1
    while beg < len
        isdigit(s[beg]) && break
        beg += 1
    end
    dig = lst - beg + 1
    dig < 4 && return s

    commas = div(dig - 1, 3)
    sv = Base.StringVector(len + commas)

    for i = 1:beg-1; sv[i] = s[i]; end
    cnt = dig - commas*3
    pos = beg - 1
    for i = beg:lst-3
        sv[pos += 1] = s[i]
        (cnt -= 1) == 0 && (cnt = 3; sv[pos += 1] = ',')
    end
    for i = lst-2:len; sv[i+commas] = s[i]; end
    T(sv)
end
addcommas(s) = (l = length(s); addcommas(s, l, l))

function generate_format_string(;
                                width::Int=-1,
                                precision::Int= -1,
                                leftjustified::Bool=false,
                                zeropadding::Bool=false,
                                commas::Bool=false,
                                signed::Bool=false,
                                positivespace::Bool=false,
                                alternative::Bool=false,
                                conversion::ASCIIStr="f" #aAdecEfFiosxX
                                )
    s = ['%'%UInt8]
    commas &&
        push!(s, '\'')
    alternative && in( conversion[1], "aAeEfFoxX" ) &&
        push!(s, '#')
    zeropadding && !leftjustified && width != -1 &&
        push!(s, '0')
    if signed
        push!(s, '+')
    elseif positivespace
        push!(s, ' ')
    end
    if width != -1
        leftjustified && push!(s, '-')
        append!(s, _codeunits(string( width )))
    end
    precision != -1 &&
        append!(s, _codeunits(string( '.', precision )))
    String(append!(s, _codeunits(conversion)))
end

function format( x::T;
                 width::Int=-1,
                 precision::Int= -1,
                 leftjustified::Bool=false,
                 zeropadding::Bool=false, # when right-justified, use 0 instead of space to fill
                 commas::Bool=false,
                 signed::Bool=false, # +/- prefix
                 positivespace::Bool=false,
                 stripzeros::Bool=(precision== -1),
                 parens::Bool=false, # use (1.00) instead of -1.00. Used in finance
                 alternative::Bool=false, # usually for hex
                 mixedfraction::Bool=false,
                 mixedfractionsep::UTF8Str="_",
                 fractionsep::UTF8Str="/", # num / den
                 fractionwidth::Int = 0,
                 tryden::Int = 0, # if 2 or higher,
                                  # try to use this denominator, without losing precision
                 suffix::UTF8Str="", # useful for units/%
                 autoscale::Symbol=:none, # :metric, :binary or :finance
                 conversion::ASCIIStr=""
                 ) where {T<:Real}
    checkwidth = commas
    if conversion == ""
        if T <: AbstractFloat || T <: Rational && precision != -1
            actualconv = "f"
        elseif T <: Unsigned
            actualconv = "x"
        elseif T <: Integer
            actualconv = "d"
        else
            conversion = "s"
            actualconv = "s"
        end
    else
        actualconv = conversion
    end
    signed && commas && error( "You cannot use signed (+/-) AND commas at the same time")

    T <: Rational && conversion == "s" && (stripzeros = false)
    if ( T <: AbstractFloat && actualconv == "f" || T <: Integer ) && autoscale != :none
        actualconv = "f"
        if autoscale == :metric
            scales = [
                (1e24, "Y" ),
                (1e21, "Z" ),
                (1e18, "E" ),
                (1e15, "P" ),
                (1e12, "T" ),
                (1e9,  "G"),
                (1e6,  "M"),
                (1e3,  "k") ]
            if abs(x) > 1
                for (mag, sym) in scales
                    if abs(x) >= mag
                        x /= mag
                        suffix = string(sym, suffix)
                        break
                    end
                end
            elseif T <: AbstractFloat
                smallscales = [
                    ( 1e-12, "p" ),
                    ( 1e-9,  "n" ),
                    ( 1e-6,  "μ" ),
                    ( 1e-3,  "m" ) ]
                for (mag,sym) in smallscales
                    if abs(x) < mag*10
                        x /= mag
                        suffix = string(sym, suffix)
                        break
                    end
                end
            end
        else
            if autoscale == :binary
                scales = [
                    (1024.0 ^8,  "Yi" ),
                    (1024.0 ^7,  "Zi" ),
                    (1024.0 ^6,  "Ei" ),
                    (1024.0 ^5,  "Pi" ),
                    (1024.0 ^4,  "Ti" ),
                    (1024.0 ^3,  "Gi"),
                    (1024.0 ^2,  "Mi"),
                    (1024.0,     "Ki")
                ]
            else # :finance
                scales = [
                    (1e12, "t" ),
                    (1e9,  "b"),
                    (1e6,  "m"),
                    (1e3,  "k") ]
            end
            for (mag, sym) in scales
                if abs(x) >= mag
                    x /= mag
                    suffix = string(sym, suffix)
                    break
                end
            end
        end
    end

    nonneg = x >= 0
    fractional = 0
    if T <: Rational && mixedfraction
        actualconv = "d"
        actualx = trunc( Int, x )
        fractional = abs(x) - abs(actualx)
    else
        actualx = (parens && !in( actualconv[1], "xX" )) ? abs(x) : x
    end
    s = cfmt( generate_format_string( width=width,
                                      precision=precision,
                                      leftjustified=leftjustified,
                                      zeropadding=zeropadding,
                                      commas=commas,
                                      signed=signed,
                                      positivespace=positivespace,
                                      alternative=alternative,
                                      conversion=actualconv
                                      ),
              actualx)

    if T <:Rational && conversion == "s"
        if mixedfraction && fractional != 0
            num = fractional.num
            den = fractional.den
            if tryden >= 2 && mod( tryden, den ) == 0
                num *= div(tryden,den)
                den = tryden
            end
            fs = string( num, fractionsep, den)
            length(fs) < fractionwidth &&
                (fs = string(repeat( "0", fractionwidth - length(fs) ), fs))
            s = (actualx != 0
                 ? string(rstrip(s), mixedfractionsep, fs)
                 : (nonneg ? fs : string('-', fs)))
            checkwidth = true
        elseif !mixedfraction
            s = replace( s, "//" => fractionsep )
            checkwidth = true
        end
    elseif stripzeros && in( actualconv[1], "fFeEs" )
        dpos = findfirst( isequal('.'), s )
        dpos === nothing && (dpos = length(s))
        if actualconv[1] in "eEs"
            epos = findfirst(isequal(actualconv[1] == 'E' ? 'E' : 'e'), s)
            rpos = (epos === nothing) ? length( s ) : (epos-1)
        else
            rpos = length(s)
        end
        # rpos at this point is the rightmost possible char to start
        # stripping
        stripfrom = rpos+1
        for i = rpos:-1:dpos+1
            if s[i] == '0'
                stripfrom = i
            elseif s[i] ==' '
                continue
            else
                break
            end
        end
        if stripfrom <= rpos
            # everything after decimal is 0, so strip the decimal too
            s = string(s[1:stripfrom-1-(stripfrom == dpos+1)], s[rpos+1:end])
            checkwidth = true
        end
    end

    s = string(s, suffix)

    if parens && !in( actualconv[1], "xX" )
        # if zero or positive, we still need 1 white space on the right
        s = nonneg ? string(' ', strip(s), ' ') : string('(', strip(s), ')')
        checkwidth = true
    end

    if checkwidth && width != -1
        if (len = length(s) - width) > 0
            s = replace( s, " " => ""; count=len )
            if (len = length(s) - width) > 0
                endswith(s, " ") && (s = reverse(replace(reverse(s), " " => ""; count=len)))
                (len = length(s) - width) > 0 && (s = replace( s, "," => ""; count=len ))
            end
        elseif len < 0
            # Todo: should use lpad or rpad here, can be more efficient
            s = leftjustified ? string(s, repeat( " ", -len )) : string(repeat( " ", -len), s)
        end
    end

    s
end
