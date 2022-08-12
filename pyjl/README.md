
<h1 align="center"><b>PyJL</b></h1>

<div align="center">
    <img align="center" src="https://drive.google.com/uc?export=view&id=1DLeY_tGgVGRzoO7O7lnTb-ZxetfT9qUw" alt="PyJL" width="400">
</div>

## What is PyJL?
PyJL is Py2Many's transpiler implementation that translates Python into Julia. We are developing PyJL to generate human-readable and pragmatically correct Julia source code with the aim of speeding up the development of Julia by translating Python libraries. 

## External Code Annotation Mechanism
PyJL includes a code annotation mechanism, which uses `JSON` or `Yaml` files to specify annotations. Currently, programmers can specify type hints on function definitions and also specify decorators. 

## Inference Mechanism
Having a type-inference mechanism is crucial to transpile Python source code to Julia, as the translation outcome might depend on the type information available. Py2Many already offers a type-inference mechanism, which we extended with new inference rules for PyJL.

The inference mechanism in Py2Many is implemented using a define-use set. This mechanism recursively walks the AST and aggregates type information from node assignments for each scope. 
The defined scopes are more extensive than Python's scopes, to cover the scoping rules of all supported languages. The current scopes include `module`s, `function`s, `class`es, `for` and `while` loops, `if` statements, and `with`-statements. 

Similarly to MyPy, PyJL also requires programmers to annotate function definitions. PyJL uses these definitions to mitigate type instability and to translate operations that depend on the operand types.

Lastly, PyJL strictly enforces static typing using Python's type hints. Therefore, any user-annotated variables are only allowed to have one type within their scope.

Currently, we are considering the addition of an external type inference mechanism. Our considerations include [pytype](https://github.com/google/pytype) or a [MaxSMT based approach](https://link.springer.com/chapter/10.1007/978-3-319-96142-2_2) to infer types.

## Requirements:
- Python 3
- Julia 1.6, 1.7
- Some features require the following Julia Packages:
  - [JuliaFormatter.jl](https://github.com/domluna/JuliaFormatter.jl) - Format Julia Files
  - [ResumableFunctions.jl](https://github.com/BenLauwens/ResumableFunctions.jl) - for yield mapping
  - [SuperEnum.jl](https://github.com/kindlychung/SuperEnum.jl) - support Python string Enumerators
  - [Classes.jl](https://github.com/rjplevin/Classes.jl) - Suport a Python-like class translation alternative
  - [GZip.jl](https://github.com/JuliaIO/GZip.jl) - allow working with gzip files
  - [OrderedCollections.jl](https://github.com/JuliaCollections/OrderedCollections.jl) - Ensures that the output of Julia's collections, such as Dictionaries or Sets, respects the insertion order
  <!-- - [DataClass.jl](https://github.com/MiguelMarcelino/Dataclass.jl") - uses a macro to map Python's dataclass decorator -->

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
  - [x] `as`
  - [x] `assert`
  - [ ] `async`
  - [ ] `await`
  - [x] `break`
  - [x] `class`
  - [x] `continue`
  - [x] `def`
  - [ ] `del` -> Partially supported
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
    - [x] bytesliteral
    - [x] bytesprefix
    - [ ] shortbytes
    - [ ] longbytes
    - [ ] bytesescapeseq
  - Formatted String literals
    - [x] f_string &rarr; using string interpolation
    - [ ] replacement_field
    - [x] f_expression
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
- Delimiters (PLR 2.6) &rarr; Read [issue #21](https://github.com/MiguelMarcelino/py2many/issues/21) &rarr; check `InplaceOps`
  - [x] `+=`
  - [ ] `-=`
  - [x] `*=` &rarr; TODO: verify
  - [ ] `/=`
  - [ ] `//=`
  - [ ] `%=`
  - [x] `&=` &rarr; TODO: verify
  - [ ] `|=` &rarr; TODO: verify
  - [ ] `>>=` &rarr; TODO: verify
  - [ ] `<<=` &rarr; TODO: verify
  - [ ] `^=`
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
  - [x] `__init__`
  - [ ] `__new__`, `__del__`, `__repr__`, <br/>`__str__`, `__bytes__`, `__format__`, `__lt__`,  <br/>`__le__`, `__eq__`, `__ne__`, `__gt__`, `__ge__` <br/> `__hash__`, `__bool__` <br/>

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
  - [x] `/`
  - [x] `//`
  - [x] `%`
  - [x] `@` matrix multiplication
- Shift operations (PLR 6.8)
  - [x] `<<`
  - [x] `>>`
- Binary bitwise operations (PLR 6.9)
  - [ ] `&` &rarr; TODO: verify
  - [ ] `|` &rarr; TODO: verify
  - [ ] `^` &rarr; TODO: verify
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
  - [x] expression_list
  - [x] starred_list
  - [x] starred_expression
  - [x] starred_item

#
## Additional Functionalities
- Python `with` statement uses context managers to allocate and release resources. Julia's do-block does not use context managers but is built with the same idea. (https://book.pythontips.com/en/latest/context_managers.html)
- `with` and `try-finally` can be used for similar purposes. (Example of file closing)
- `del` keyword mapping (probably not possible)
- `__repr__` requires a `show()` implementation: show(io::IO, o::object) = print(io, "$(o.attr)")


## Code Formatting
For code formatting, PyJL uses JuliaFormatter.jl. If you want to specify your own formatting options, you need to create a `.JuliaFormatter.toml` file. A sample file is provided in the `pyjl/formatter` folder. You need to place this file in the same directory (or any parent directory) you are transpiling. You can find more instructions [here](https://github.com/domluna/JuliaFormatter.jl).


## Test Status
All tests that are striked are currently failing

- `assert.jl`
- `assign_list_test.jl`
- `~~asyncio_test.jl~~`
- `binit.jl`
- `binomial_coefficient.jl`
- `bin_op.jl`
- `bin_op_no_annotations.jl`
- `bitops.jl`
- `branch.jl`
- `bubble_sort.jl`
- `built_ins.jl`
- `bytearray_test.jl`
- `byte_literals.jl`
- `classes.jl`
- `classes_dataclass.jl` --> Review (change special methods)
- `classes_scopes.jl`
- `cls.jl`
- `comb_sort.jl`
- `comment_unsupported.jl`
- `complex.jl`
- `~~coverage.jl~~` --> Fails because of next
- `datatypes.jl`
- `~~demorgan.jl~~` --> Fails because Julia has no check_sat function
- `dict.jl`
- `equations.jl`
- `~~exceptions.jl~~` --> ZeroDivisionError
- `~~expression_lists.jl~~` --> Splat
- `fib.jl`
- `find_factors.jl`
- `fib_with_argparse.jl`
- `f_string.jl`
- `generator_expressions.jl`
- `global.jl`
- `global2.jl`
- `import.jl`
- `infer.jl`
- `infer_ops.jl`
- `int_enum.jl`
- `join_test.jl`
- `lambda.jl`
- `langcomp_bench.jl` --> All except `del`
- `~~library_import.jl~~` --> No support for datetime
- `list_op.jl`
- `literals.jl`
- `match_case_test.jl` --> Only Python 9 is supported
- `math_ops.jl`
- `nested_dict.jl`
- `newman_conway_sequence.jl`
- `n_bonacci_sequence.jl`
- `print.jl`
- `rect.jl`
- `~~sealed.jl~~` --> No field VALUE
- `smt_types.jl`
- `str_enum.jl`
- `subscript_test.jl`
- `sys_argv.jl`
- `sys_exit.jl`
- `test_indexing.jl`
- `unary_op.jl`
- `walruss.jl`
- `~~with_cntx_manager.jl~~` --> No Package textwrap
- `~~with_open.jl~~` --> NamedTempFile
- `write_stdout.jl`
- `yield_from_test.jl`
- `yield_test.jl`

#
## Keywords
- PLR - Python Language Reference (Based on version 3.9.7)
