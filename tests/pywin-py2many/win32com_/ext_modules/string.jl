#= A collection of string constants.

Public module variables:

whitespace -- a string containing all ASCII whitespace
ascii_lowercase -- a string containing all ASCII lowercase letters
ascii_uppercase -- a string containing all ASCII uppercase letters
ascii_letters -- a string containing all ASCII letters
digits -- a string containing all ASCII decimal digits
hexdigits -- a string containing all ASCII hexadecimal digits
octdigits -- a string containing all ASCII octal digits
punctuation -- a string containing all ASCII punctuation characters
printable -- a string containing all ASCII characters considered printable

 =#
export ascii_letters,
    ascii_lowercase,
    ascii_uppercase,
    capwords,
    digits,
    hexdigits,
    octdigits,
    printable,
    punctuation,
    whitespace,
    Formatter,
    Template
import _string
whitespace = " \t\n\r\v\f"
abstract type AbstractTemplate end
abstract type AbstractFormatter end
ascii_lowercase = "abcdefghijklmnopqrstuvwxyz"
ascii_uppercase = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
ascii_letters = ascii_lowercase * ascii_uppercase
digits = "0123456789"
hexdigits = digits * "abcdef" * "ABCDEF"
octdigits = "01234567"
punctuation = "!\"#\$%&\'()*+,-./:;<=>?@[\\]^_`{|}~"
printable = digits * ascii_letters * punctuation * whitespace
function capwords(s, sep = nothing)
    #= capwords(s [,sep]) -> string

        Split the argument into words using split, capitalize each
        word using capitalize, and join the capitalized words using
        join.  If the optional second argument sep is absent or None,
        runs of whitespace characters are replaced by a single space
        and leading and trailing whitespace are removed, otherwise
        sep is used to split and join the words.

         =#
    return join((capitalize(x) for x in split(s, sep)), sep || " ")
end

_sentinel_dict = Dict()
mutable struct Template <: AbstractTemplate
    #= A string class for supporting $-substitutions. =#
    pattern
    template
    braceidpattern
    delimiter::String
    flags
    idpattern::String

    Template(
        pattern,
        template,
        braceidpattern = nothing,
        delimiter::String = "\$",
        flags = _re.IGNORECASE,
        idpattern::String = "(?a:[_a-z][_a-z0-9]*)",
    ) = new(pattern, template, braceidpattern, delimiter, flags, idpattern)
end
function __init_subclass__(cls)
    __init_subclass__(super())
    if "pattern" ∈ cls.__dict__
        pattern = cls.pattern
    else
        delim = escape(_re, cls.delimiter)
        id = cls.idpattern
        bid = cls.braceidpattern || cls.idpattern
        pattern = "\n            $(delim)(?:\n              (?P<escaped>$(delim))  |   # Escape sequence of two delimiters\n              (?P<named>$(id))       |   # delimiter and a Python identifier\n              {(?P<braced>$(bid))} |   # delimiter and a braced identifier\n              (?P<invalid>)             # Other ill-formed delimiter exprs\n            )\n            "
    end
    cls.pattern = compile(_re, pattern, cls.flags | _re.VERBOSE)
end

function _invalid(self::Template, mo)
    i = start(mo, "invalid")
    lines = splitlines(self.template[begin:i], true)
    if !(lines)
        colno = 1
        lineno = 1
    else
        colno = i - length(join(lines[begin:-1], ""))
        lineno = length(lines)
    end
    throw(ValueError("Invalid placeholder in string: line %d, col %d" % (lineno, colno)))
end

function substitute()
    if mapping == _sentinel_dict
        mapping = kws
    elseif kws
        mapping = _ChainMap(kws, mapping)
    end
    function convert(mo)::String
        named = group(mo, "named") || group(mo, "braced")
        if named != nothing
            return string(mapping[named+1])
        end
        if group(mo, "escaped") != nothing
            return self.delimiter
        end
        if group(mo, "invalid") != nothing
            _invalid(self, mo)
        end
        throw(ValueError("Unrecognized named group in pattern", self.pattern))
    end

    return sub(self.pattern, convert, self.template)
end

function safe_substitute()
    if mapping == _sentinel_dict
        mapping = kws
    elseif kws
        mapping = _ChainMap(kws, mapping)
    end
    function convert(mo)::String
        named = group(mo, "named") || group(mo, "braced")
        if named != nothing
            try
                return string(mapping[named+1])
            catch exn
                if exn isa KeyError
                    return group(mo)
                end
            end
        end
        if group(mo, "escaped") != nothing
            return self.delimiter
        end
        if group(mo, "invalid") != nothing
            return group(mo)
        end
        throw(ValueError("Unrecognized named group in pattern", self.pattern))
    end

    return sub(self.pattern, convert, self.template)
end

__init_subclass__(Template)
mutable struct Formatter <: AbstractFormatter
end
function format()
    return vformat(self, format_string, args, kwargs)
end

function vformat(self::Formatter, format_string, args, kwargs)
    used_args = set()
    result, _ = _vformat(self, format_string, args, kwargs, used_args, 2)
    check_unused_args(self, used_args, args, kwargs)
    return result
end

function _vformat(
    self::Formatter,
    format_string,
    args,
    kwargs,
    used_args,
    recursion_depth,
    auto_arg_index = 0,
)::Tuple
    if recursion_depth < 0
        throw(ValueError("Max string recursion exceeded"))
    end
    result = []
    for (literal_text, field_name, format_spec, conversion) in parse(self, format_string)
        if literal_text
            push!(result, literal_text)
        end
        if field_name != nothing
            if field_name == ""
                if auto_arg_index == false
                    throw(
                        ValueError(
                            "cannot switch from manual field specification to automatic field numbering",
                        ),
                    )
                end
                field_name = string(auto_arg_index)
                auto_arg_index += 1
            elseif isdigit(field_name)
                if auto_arg_index
                    throw(
                        ValueError(
                            "cannot switch from manual field specification to automatic field numbering",
                        ),
                    )
                end
                auto_arg_index = false
            end
            obj, arg_used = get_field(self, field_name, args, kwargs)
            add(used_args, arg_used)
            obj = convert_field(self, obj, conversion)
            format_spec, auto_arg_index =
                _vformat(self, format_spec, args, kwargs, used_args, recursion_depth - 1)
            push!(result, format_field(self, obj, format_spec))
        end
    end
    return (join(result, ""), auto_arg_index)
end

function get_value(self::Formatter, key, args, kwargs)
    if isa(key, int)
        return args[key+1]
    else
        return kwargs[key+1]
    end
end

function check_unused_args(self::Formatter, used_args, args, kwargs)
    #= pass =#
end

function format_field(self::Formatter, value, format_spec)
    return value
end

function convert_field(self::Formatter, value, conversion)::String
    if conversion === nothing
        return value
    elseif conversion == "s"
        return string(value)
    elseif conversion == "r"
        return repr(value)
    elseif conversion == "a"
        return ascii(value)
    end
    throw(ValueError("Unknown conversion specifier $(conversion!s)"))
end

function parse(self::Formatter, format_string)
    return formatter_parser(_string, format_string)
end

function get_field(self::Formatter, field_name, args, kwargs)::Tuple
    first, rest = formatter_field_name_split(_string, field_name)
    obj = get_value(self, first, args, kwargs)
    for (is_attr, i) in rest
        if is_attr
            obj = getfield(obj, :i)
        else
            obj = obj[i+1]
        end
    end
    return (obj, first)
end
