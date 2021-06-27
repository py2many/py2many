# Introduction

py2many supports a subset of python and mixes it with concepts from other statically typed languages that make it easy to write type safe code and assist the transpiler as well.

# Supported Features

## Types
* int, float, bool, str, bytes
* Fixed width signed ints (i8, i16, i32, i64)
* Fixed width unsigned ints (u8, u16, u32, u64)
* Homogenous List, Set, Dicts
* Explicit type coersion (bool(1))

## Operators
* Unary operators
* Binary operators
* Bitwise operators
* Math (pow, floor, max, min)
* Ternary operators (if foo 1 else 2)

## Control Flow
* For loops
* While loops
* Functions
* if-then-else

## Statements
* Assignments
* Annotated assignments (a: i8 = 10)
* Augmented assignments (a += 5)

## Object oriented programming
* Classes
* Dataclasses
* Composition

## Secure programming
* Overflow protection (i8 + i8 is auto inferred as i16) for addition

## Functional programming
* Algebraic data types via sealed classes (rust only)
* Result[T, E] (rust only)
* Lambdas
* Enums (int and str enums)

## Misc
* asyncio (rust only)
* imports
* asserts, prints
* standalone scripts using `if __name__ == "__main__":`, `sys.argv` and `sys.exit(code)`

# Not Supported Features

* Dynamic typing. Every variable should have an explicit type or the type inference code must be able to infer the type.
* Eval, metaclasses, monkey patching
* Introspection. isinstance(...) and friends
* Aribtrary precision ints. Int transpiles to i32.
* Heterogenous List, Set, Dicts

# TODO
* Underflow protection (for subtraction and possibly other ops)
* List, Dict, Set comprehensions
