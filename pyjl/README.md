
<h1 align="center"><b>PyJL</b></h1>

<div align="center">
    <img align="center" src="https://drive.google.com/uc?export=view&id=1DLeY_tGgVGRzoO7O7lnTb-ZxetfT9qUw" alt="PyJL" width="400">
</div>

## What is PyJL?
PyJL is Py2Many's transpiler implementation that translates Python into Julia. The goal of PyJL is to to produce human-readable Julia source code and preserve the pragmatics of the Julia programming language. The aim is to transpile Python source-code that has been judiciously annotated using Python's type hints.

## Code Annotation Mechanism
PyJL's future iterations should also include a code annotation mechanism. The current mecanism is very basic and uses `JSON` or `Yaml` files to specify annotations. The goal is to integrate a DSL to allow programmers to specify code annotations and code generation mechanisms for the transpiler. The LARA DSL appears to fulfil our goals in this regard, although this is still under study.

## Inference Mechanism
The current mechanism included in PyJL only uses Python's type hints to correctly map operations and expressions to Julia. Operator overloading is currently one of the focuses of the translation. To solve these problems, a type inference mechanism could be integrated into PyJL. Current options include [MyPy](http://mypy-lang.org/) or a [MaxSMT based approach](https://link.springer.com/chapter/10.1007/978-3-319-96142-2_2) to infer types.


#
## PyJL Status
The following section describes the currently supported features of PyJL. All marked boxes are features that are supported by PyJL. All unmarked boxes are either unsupported or don't have tests verifying them.

### <ins>Lexical Translation</ins>
- Line Structure (PLR 2.1)
  - [ ] Comments
  - [ ] Encoding Declarations
  - [ ] Line Joining
  - [ ] Implicit Line Joining
- Keywords (PLR 2.3)
  - [x] `False`
  - [x] `True`
  - [x] `None`
  - [x] `and`
  - [ ] `as`
  - [x] `assert`
  - [ ] `async`
  - [ ] `await`
  - [x] `break`
  - [x] `class`
  - [x] `continue`
  - [x] `def`
  - [ ] `del`
  - [x] `elif`
  - [x] `else`
  - [x] `except`
  - [x] `finally`
  - [x] `for`
  - [x] `from` (for imports)
  - [ ] `global`
  - [x] `if`
  - [x] `import`
  - [x] `in`
  - [x] `is`
  - [x] `lambda`
  - [ ] `nonlocal` 
  - [x] `not`
  - [x] `or`
  - [x] `pass` (empty block)
  - [x] `raise`
  - [x] `return`
  - [x] `try`
  - [x] `while`
  - [ ] `with`
  - [x] `yield`
- Literals (PLR 2.4)
  - String
    - [x] stringliteral
    - [ ] stringprefix
    - [x] shortstring
    - [ ] longstring 
    - [ ] stringescape
  - Bytes
    - [ ] bytesliteral
    - [ ] bytesprefix
    - [ ] shortbytes
    - [ ] longbytes
    - [ ] bytesescapeseq
  - Formatted String literals
    - [x] f_string &rarr; using string interpolation
    - [ ] replacement_field
    - [ ] f_expression
    - [ ] conversion
    - [ ] format_spec
    - [ ] literal_char
  - Integer literals
    - [x] integer 
    - [x] decinteger 
    - [x] bininteger &rarr; use #type: BLiteral 
    - [x] octinteger &rarr; use #type: OLiteral 
    - [x] hexinteger &rarr; use #type: HLiteral 
    - [x] nonzerodigit
    - [x] digit
    - [x] bindigit
    - [x] octdigit
    - [x] hexdigit
  - Floating Point literals
    - [x] floatnumber
    - [x] pointfloat
    - [x] exponentfloat
    - [x] digitpart
    - [x] fraction
    - [x] exponent
  - Imaginary literals
    - [x] imagnumber
- Operators (PLR 2.5)
  - See expressions below
- Delimiters (PLR 2.6) &rarr; only relevant ones included
  - [x] `+=`, `-=`, `*=`, `/=`, `//=`, `%=`, `&=`, `|=`, `^=`, `>>=`, `<<=` &rarr; direct translation
  - [ ] `@=`
  - [ ] `**=`

### <ins>Data Model</ins>
- Type Hierarchy (PLR 3.2)
  - [x] None
  - [ ] NotImplemented
  - [x] Ellipsis
  - Number
    - Integral
      - [x] Integers
      - [x] Booleans
    - Real
      - [x] Float
    - Complex
      - [x] Complex
  - Sequences 
    - Immutable sequences
      - [x] Strings
      - [x] Tuples
      - [x] Bytes
    - Mutable Sequences
      - [x] Lists
      - [x] Byte Arrays (requires test)
  - Set types
    - [x] Set
    - [ ] Frozen Set
  - Mappings
    - [x] Dictionaries
  - Callable types
    - [ ] User-defined functions
    - [ ] Instance Methods
    - [x] Generator functions
    - [ ] Coroutine functions
    - [ ] Asynchronous generator functions
    - [x] Built-in functions (subset)
    - [x] Built-in methods (subset)
    - [x] Classes
    - [x] Class Instances
  - Modules
    - [x] Import
- Special method names
  - [ ] `__new__`, `__init__`, `__del__`, `__repr__`, <br/>`__str__`, `__bytes__`, `__format__`, `__lt__`,  <br/>`__le__`, `__eq__`, `__ne__`, `__gt__`, `__ge__` <br/> `__hash__`, `__bool__` <br/> &rarr; some supported in `@dataclass` macro

### <ins>Expressions</ins>
Expression mapping includes the mapping of Python's overloading. The transpiler phase uses the information added by previous phases to correctly translate expressions to Julia.

- Atoms (PLR 6.2)
  - [x] List displays
  - [x] Set Displays
  - [x] Dictionary displays
  - [x] Generator expressions
  - [x] Yield expressions
- Primaries (PLR 6.3)
  - [x] Attribute References
  - [x] Subscriptions
  - [x] Slicing 
  - Calls (PLR 6.3.4)
    - [x] call 
    - [x] argument_list
    - [x] positional_arguments
    - [x] positional_item 
    - [ ] starred_and_keyword
    - [x] keyword_arguments
    - [x] keyword_item
- Unary Arithmetic and Bitwise operations (PLR 6.6)
  - [x] `**` (power)
  - [x] `-` (subtract)
  - [x] `+` (add)
  - [x] `~` (invert)
- Binary arithmetic operations (PLR 6.7)
  - [x] `+`
  - [x] `-`
  - [x] `*`
  - [ ] `/`
  - [ ] `//`
  - [ ] `%`
  - [ ] `@` matrix multiplication
- Shift operations (PLR 6.8)
  - [ ] `<<`
  - [ ] `>>`
- Binary bitwise operations (PLR 6.9)
  - [ ] `&`
  - [ ] `|`
  - [ ] `^`
- Comparison (PLR 6.10)
  - [x] `<`
  - [x] `>`
  - [x] `<=`
  - [x] `>=`
  - [x] `==`
  - [x] `!=`
- Boolean
  - [x] `or`
  - [x] `and`
  - [x] `not`
- Assignment (PLR 6.12)
  - [x] `:=` 
- Conditional expressions (PLR 6.13)
  - [x] Ternary operators
- Lambdas (PLR 6.14)
  - [x] lambda expressions
- Expression lists (PLR 6.15)
  - [ ] expression_list
  - [ ] starred_list
  - [ ] starred_expression
  - [ ] starred_item
  

#
## Known Errors
- `ZeroDivisionException` does not happen in Julia. Julia instead returns `Inf`.
  - Example: Raising 0.0 to a negative number results in `ZeroDivisionException` in Python but returns Inf in Julia.

#
## Missing Tests
- ~~Test `raise` keyword~~
  - ~~Add to: `tests/cases/exceptions.py`~~
- Test Literal translation (escape sequences PLR 2.4.1)
  - ~~Create new `tests/cases/literals_string.py`~~
  - ~~Create new `tests/cases/literals_bytes.py`~~
  - ~~Create new `tests/cases/literals_integer.py`~~
  - ~~Create new `tests/cases/literals_ floating_point.py`~~
  - ~~Change f_string to use new `"$var"` Julia syntax in `tests/cases/f_string.py` (PLR 2.4.3)~~
  - Create new `tests/cases/f_expression.py` (PLR 2.4.3)
- Check if all Operator overloading cases are included
  - Check `tests/cases/bin_op.py`
- Check bytearray translation
  - Create new `tests/cases/bytearray.py`
- Check set translation
  - Create new `tests/cases/set.py`
- Check callable types translation
  - Create new `tests/cases/classes_callable.py`
- Check coroutine functions `async def` and expressions `await`, `async with` and `async for`
  - Create new `tests/cases/coroutine_functions.py`
- Check asyncrhonous generator functions `async def` and `async for`
  - Create new `tests/cases/async_gen_functions.py`
- Create new `tests/cases/math_ops.py` to test `math.sin()`, `math.cos()`, ...
- Test list slicing
  - Add to `tests/cases/list_op.py`
- Check keyword and starred arguments
  - Create new `tests/cases/calls.py`
- Test arithmetic power operations
  - Add to `tests/cases/bin_op.py`
- Test expression lists
  - Create new `tests/cases/expressions.py`
- Add `visit_LShift` and `visit_RShift` to transpiler
- Translate match-case to Julia. 
  - Add to `tests/cases/match_case.py`

#
## Keywords
- PLR - Python Language Reference (Based on version 3.9.7)