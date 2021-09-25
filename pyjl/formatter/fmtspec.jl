# formatting specification

# formatting specification language
#
#  spec  ::= [[fill]align][sign][#][0][width][,][.prec][type]
#  fill  ::= <any character>
#  align ::= '<' | '>'
#  sign  ::= '+' | '-' | ' '
#  width ::= <integer>
#  prec  ::= <integer>
#  type  ::= 'b' | 'c' | 'd' | 'e' | 'E' | 'f' | 'F' | 'g' | 'G' |
#            'n' | 'o' | 'x' | 'X' | 's'
#
# Please refer to http://docs.python.org/2/library/string.html#formatspec
# for more details
#

## FormatSpec type

const _numtypchars = Set(['b', 'd', 'e', 'E', 'f', 'F', 'g', 'G', 'n', 'o', 'x', 'X'])

_tycls(c::AbstractChar) =
    (c == 'd' || c == 'n' || c == 'b' || c == 'o' || c == 'x') ? 'i' :
    (c == 'e' || c == 'f' || c == 'g') ? 'f' :
    (c == 'c') ? 'c' :
    (c == 's') ? 's' :
    error("Invalid type char $(c)")

struct FormatSpec
    cls::Char    # category: 'i' | 'f' | 'c' | 's'
    typ::Char
    fill::Char
    align::Char
    sign::Char
    width::Int
    prec::Int
    ipre::Bool   # whether to prefix 0b, 0o, or 0x
    zpad::Bool   # whether to do zero-padding
    tsep::Bool   # whether to use thousand-separator

    function FormatSpec(typ::AbstractChar;
                        fill::AbstractChar=' ',
                        align::AbstractChar='\0',
                        sign::AbstractChar='-',
                        width::Int=-1,
                        prec::Int=-1,
                        ipre::Bool=false,
                        zpad::Bool=false,
                        tsep::Bool=false)

        align == '\0' && (align = (typ in _numtypchars) ? '>' : '<')
        cls = _tycls(lowercase(typ))
        cls == 'f' && prec < 0 && (prec = 6)
        new(cls, Char(typ), Char(fill), Char(align), Char(sign), width, prec, ipre, zpad, tsep)
    end

    # copy constructor with overrides
    function FormatSpec(spec::FormatSpec;
                        fill::AbstractChar=spec.fill,
                        align::AbstractChar=spec.align,
                        sign::AbstractChar=spec.sign,
                        width::Int=spec.width,
                        prec::Int=spec.prec,
                        ipre::Bool=spec.ipre,
                        zpad::Bool=spec.zpad,
                        tsep::Bool=spec.tsep)
        new(spec.cls, spec.typ, Char(fill), Char(align), Char(sign), width, prec, ipre, zpad, tsep)
    end
end

function show(io::IO, fs::FormatSpec)
    println(io, "$(typeof(fs))")
    println(io, "  cls   = $(fs.cls)")
    println(io, "  typ   = $(fs.typ)")
    println(io, "  fill  = $(fs.fill)")
    println(io, "  align = $(fs.align)")
    println(io, "  sign  = $(fs.sign)")
    println(io, "  width = $(fs.width)")
    println(io, "  prec  = $(fs.prec)")
    println(io, "  ipre  = $(fs.ipre)")
    println(io, "  zpad  = $(fs.zpad)")
    println(io, "  tsep  = $(fs.tsep)")
end

## parse FormatSpec from a string

const _spec_regex = r"^(.?[<>])?([ +-])?(#)?(\d+)?(,)?(.\d+)?([bcdeEfFgGnosxX])?$"

function FormatSpec(s::AbstractString)
    # default spec
    _fill = ' '
    _align = '\0'
    _sign = '-'
    _width = -1
    _prec = -1
    _ipre = false
    _zpad = false
    _tsep = false
    _typ = 's'

    if !isempty(s)
        m = match(_spec_regex, s)
        m == nothing && error("Invalid formatting spec: $(s)")

        (a1, a2, a3, a4, a5, a6, a7) = m.captures

        # a1: [[fill]align]
        if a1 != nothing
            if length(a1) == 1
                _align = a1[1]
            else
                _fill = a1[1]
                _align = a1[nextind(a1, 1)]
            end
        end

        # a2: [sign]
        a2 == nothing || (_sign = a2[1])

        # a3: [#]
        a3 == nothing || (_ipre = true)

        # a4: [0][width]
        if a4 != nothing
            if a4[1] == '0'
                _zpad = true
                length(a4) > 1 && (_width = parse(Int, a4[2:end]))
            else
                _width = parse(Int, a4)
            end
        end

        # a5: [,]
        a5 == nothing || (_tsep = true)

        # a6 [.prec]
        a6 == nothing || (_prec = parse(Int, a6[2:end]))

        # a7: [type]
        a7 == nothing || (_typ = a7[1])
    end

    FormatSpec(_typ;
               fill=_fill,
               align=_align,
               sign=_sign,
               width=_width,
               prec=_prec,
               ipre=_ipre,
               zpad=_zpad,
               tsep=_tsep)
end # function FormatSpec


## formatted printing using a format spec

mutable struct _Dec end
mutable struct _Oct end
mutable struct _Hex end
mutable struct _HEX end
mutable struct _Bin end

_srepr(x) = repr(x)
_srepr(x::AbstractString) = x
_srepr(x::Symbol) = string(x)
_srepr(x::AbstractChar) = string(x)
_srepr(x::Enum) = string(x)

function printfmt(io::IO, fs::FormatSpec, x)
    cls = fs.cls
    ty = fs.typ
    if cls == 'i'
        ix = Integer(x)
        ty == 'd' || ty == 'n' ? _pfmt_i(io, fs, ix, _Dec()) :
        ty == 'x' ? _pfmt_i(io, fs, ix, _Hex()) :
        ty == 'X' ? _pfmt_i(io, fs, ix, _HEX()) :
        ty == 'o' ? _pfmt_i(io, fs, ix, _Oct()) :
        _pfmt_i(io, fs, ix, _Bin())
    elseif cls == 'f'
        fx = float(x)
        if isfinite(fx)
            ty == 'f' || ty == 'F' ? _pfmt_f(io, fs, fx) :
            ty == 'e' || ty == 'E' ? _pfmt_e(io, fs, fx) :
            error("format for type g or G is not supported yet (use f or e instead).")
        else
            _pfmt_specialf(io, fs, fx)
        end
    elseif cls == 's'
        _pfmt_s(io, fs, _srepr(x))
    else # cls == 'c'
        _pfmt_s(io, fs, Char(x))
    end
end

printfmt(fs::FormatSpec, x) = printfmt(_stdout(), fs, x)

pyfmt(fs::FormatSpec, x) = (buf = IOBuffer(); printfmt(buf, fs, x); String(take!(buf)))
pyfmt(spec::AbstractString, x) = pyfmt(FormatSpec(spec), x)
