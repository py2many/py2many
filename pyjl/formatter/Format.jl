"""
Format.jl

This package provides various functions to provide formatted output,
either in a fashion similar to C printf or Python format strings.

## Python-style Types and Functions

#### Types to Represent Formats

This package has two types ``FormatSpec`` and ``FormatExpr`` to represent a format specification.

In particular, ``FormatSpec`` is used to capture the specification of a single entry. One can compile a format specification string into a ``FormatSpec`` instance as

```julia
fspec = FormatSpec("d")
fspec = FormatSpec("<8.4f")
```
Please refer to [Python's format specification language](http://docs.python.org/2/library/string.html#formatspec) for details.


``FormatExpr`` captures a formatting expression that may involve multiple items. One can compile a formatting string into a ``FormatExpr`` instance as

```julia
fe = FormatExpr("{1} + {2}")
fe = FormatExpr("{1:d} + {2:08.4e} + {3|>abs2}")
```
Please refer to [Python's format string syntax](http://docs.python.org/2/library/string.html#format-string-syntax) for details.


**Note:** If the same format is going to be applied for multiple times. It is more efficient to first compile it.


#### Formatted Printing

One can use ``printfmt`` and ``printfmtln`` for formatted printing:

- **printfmt**(io, fe, args...)

- **printfmt**(fe, args...)

    Print given arguments using given format ``fe``. Here ``fe`` can be a formatting string, an instance of ``FormatSpec`` or ``FormatExpr``.
    
    **Examples**
    
    ```julia
    printfmt("{1:>4s} + {2:.2f}", "abc", 12) # --> print(" abc + 12.00")
    printfmt("{} = {:#04x}", "abc", 12) # --> print("abc = 0x0c") 
    
    fs = FormatSpec("#04x")
    printfmt(fs, 12)   # --> print("0x0c")
    
    fe = FormatExpr("{} = {:#04x}")
    printfmt(fe, "abc", 12)   # --> print("abc = 0x0c")
    ```

    **Notes**

    If the first argument is a string, it will be first compiled into a ``FormatExpr``, which implies that you can not use specification-only string in the first argument.

    ```julia
    printfmt("{1:d}", 10)   # OK, "{1:d}" can be compiled into a FormatExpr instance
    printfmt("d", 10)       # Error, "d" can not be compiled into a FormatExpr instance
                            # such a string to specify a format specification for single argument

    printfmt(FormatSpec("d"), 10)  # OK
    printfmt(FormatExpr("{1:d}", 10)) # OK
    ```


- **printfmtln**(io, fe, args...)

- **printfmtln**(fe, args...)

    Similar to ``printfmt`` except that this function print a newline at the end.

#### Formatted String

One can use ``pyfmt`` to format a single value into a string, or ``format`` to format one to multiple arguments into a string using an format expression.

- **pyfmt**(fspec, a)

    Format a single value using a format specification given by ``fspec``, where ``fspec`` can be either a string or an instance of ``FormatSpec``.

- **format**(fe, args...)

    Format arguments using a format expression given by ``fe``, where ``fe`` can be either a string or an instance of ``FormatSpec``.


#### Difference from Python's Format

At this point, this package implements a subset of Python's formatting language (with slight modification). Here is a summary of the differences:

- ``g`` and ``G`` for floating point formatting have not been supported yet. Please use ``f``, ``e``, or ``E`` instead.

- The package currently provides default alignment, left alignment ``<`` and right alignment ``>``. Other form of alignment such as centered alignment ``^`` has not been supported yet.

- In terms of argument specification, it supports natural ordering (e.g. ``{} + {}``), explicit position (e.g. ``{1} + {2}``). It hasn't supported named arguments or fields extraction yet. Note that mixing these two modes is not allowed (e.g. ``{1} + {}``).

- The package provides support for filtering (for explicitly positioned arguments), such as ``{1|>lowercase}`` by allowing one to embed the ``|>`` operator, which the Python counter part does not support.

## C-style functions

The c-style part of this package aims to get around the limitation that
`@sprintf` has to take a literal string argument.
The core part is basically a c-style print formatter using the standard
`@sprintf` macro.
It also adds functionalities such as commas separator (thousands), parenthesis for negatives,
stripping trailing zeros, and mixed fractions.

### Usage and Implementation

The idea here is that the package compiles a function only once for each unique
format string within the `Format.*` name space, so repeated use is faster.
Unrelated parts of a session using the same format string would reuse the same
function, avoiding redundant compilation. To avoid the proliferation of
functions, we limit the usage to only 1 argument. Practical consideration
would suggest that only dozens of functions would be created in a session, which
seems manageable.

Usage
```julia
using Format

fmt = "%10.3f"
s = cfmt( fmt, 3.14159 ) # usage 1. Quite performant. Easiest to switch to.

fmtrfunc = generate_formatter( fmt ) # usage 2. This bypass repeated lookup of cached function. Most performant.
s = fmtrfunc( 3.14159 )

s = format( 3.14159, precision=3 ) # usage 3. Most flexible, with some non-printf options. Least performant.
```
### Speed

`cfmt`: Speed penalty is about 20% for floating point and 30% for integers.

If the formatter is stored and used instead (see the example using `generate_formatter` above),
the speed penalty reduces to 10% for floating point and 15% for integers.

### Commas

This package also supplements the lack of thousand separator e.g. `"%'d"`, `"%'f"`, `"%'s"`.

Note: `"%'s"` behavior is that for small enough floating point (but not too small),
thousand separator would be used. If the number needs to be represented by `"%e"`, no
separator is used.

### Flexible `format` function

This package contains a run-time number formatter `format` function, which goes beyond
the standard `sprintf` functionality.

An example:
```julia
s = format( 1234, commas=true ) # 1,234
s = format( -1234, commas=true, parens=true ) # (1,234)
```

The keyword arguments are (Bold keywards are not printf standard)

* width. Integer. Try to fit the output into this many characters. May not be successful.
   Sacrifice space first, then commas.
* precision. Integer. How many decimal places.
* leftjustified. Boolean
* zeropadding. Boolean
* commas. Boolean. Thousands-group separator.
* signed. Boolean. Always show +/- sign?
* positivespace. Boolean. Prepend an extra space for positive numbers? (so they align nicely with negative numbers)
* **parens**. Boolean. Use parenthesis instead of "-". e.g. `(1.01)` instead of `-1.01`. Useful in finance. Note that
  you cannot use `signed` and `parens` option at the same time.
* **stripzeros**. Boolean. Strip trailing '0' to the right of the decimal (and to the left of 'e', if any ).
   * It may strip the decimal point itself if all trailing places are zeros.
   * This is true by default if precision is not given, and vice versa.
* alternative. Boolean. See `#` alternative form explanation in standard printf documentation
* conversion. length=1 string. Default is type dependent. It can be one of `aAeEfFoxX`. See standard
  printf documentation.
* **mixedfraction**. Boolean. If the number is rational, format it in mixed fraction e.g. `1_1/2` instead of `3/2`
* **mixedfractionsep**. Default `_`
* **fractionsep**. Default `/`
* **fractionwidth**. Integer. Try to pad zeros to the numerator until the fractional part has this width
* **tryden**. Integer. Try to use this denominator instead of a smaller one. No-op if it'd lose precision.
* **suffix**. String. This strings will be appended to the output. Useful for units/%
* **autoscale**. Symbol, default `:none`. It could be `:metric`, `:binary`, or `:finance`.
    * `:metric` implements common SI symbols for large and small numbers e.g. `M`, `k`, `μ`, `n`
    * `:binary` implements common ISQ symbols for large numbers e.g. `Ti`, `Gi`, `Mi`, `Ki`
    * `:finance` implements common finance/news symbols for large numbers e.g. `b` (billion), `m` (millions)
"""
module Format

import Base.show

_stdout() = stdout
_codeunits(s) = Vector{UInt8}(codeunits(s))
m_eval(expr) = Core.eval(@__MODULE__, expr)

export FormatSpec, FormatExpr, printfmt, printfmtln, format, generate_formatter
export pyfmt, cfmt, fmt
export fmt_default, fmt_default!, reset!, default_spec, default_spec!

# Deal with mess from #16058
# Later, use Strs package!
isdefined(Main, :ASCIIStr) || (const ASCIIStr = String)
isdefined(Main, :UTF8Str)  || (const UTF8Str = String)

include("cformat.jl" )
include("fmtspec.jl")
include("fmtcore.jl")
include("formatexpr.jl")
include("fmt.jl")

end # module Format
