# Python to many CLike language transpiler

Currently supports C++ and Rust.
Considering adding Julia, Kotlin and Nim support

The main idea is that python is popular, easy to program in, but has poor runtime performance.
We can fix that by transpiling a subset of the language into a more performant, statically
typed language

Based on Julian Konchunas' pyrs
http://github.com/konchunas/pyrs

Based on Lukas Martinelli Py14
(https://github.com/lukasmartinelli/py14) and Py14/python-3
(https://github.com/ProgVal/py14/tree/python-3) branch by Valentin
Lorentz.

## Example

Original Python version.

```python
def fib(i: int) -> int:
    if i == 0 or i == 1:
        return 1
    return fib(i - 1) + fib(i - 2)
```

Transpiled Rust code.


```rust
fn fib(i: i32) -> i32 {
    if i == 0 || i == 1 {
        return 1;
    }
    return (fib((i - 1)) + fib((i - 2)));
}
```

Transpiled C++ code.


```cpp
template <typename T1> auto fib(T1 i) {
  if (i == 0 || i == 1) {
    return 1;
  }
  return fib(i - 1) + fib(i - 2);
}
```

Transpiled Julia code.

```julia
function fib(i::Int64)::Int64
    if i == 0 || i == 1
        return 1
    end
    return (fib((i - 1)) + fib((i - 2)))
end
```

Transpiled Kotlin code.

```kotlin
fun fib(i : Int) : Int {
  if (i == 0 || i == 1) {
    return 1
  }
  return (fib((i - 1)) + fib((i - 2)))
}
```

Transpiled Nim code.

```nim

```


## Trying it out

Requirements:
- python 3
- clang
- rustc

Transpiling:

```
./py2many --cpp=1 /tmp/fib.py
./py2many --rust=1 /tmp/fib.py
./py2many --julia=1 /tmp/fib.py
./py2many --kotlin=1 /tmp/fib.py
```

Compiling:

```
clang fib.cpp
rustc fib.rs
```

## Monkeytype

Python 3.5+ type annotations can be transpiled:
```python
def cut(apple: Fruit, knife: Tool) -> Slice:
```


```rust
fn cut(apple: Fruit, knife: Tool) -> Slice {
```

## Todo list

- [x] Basic type inference for struct declaration
- [ ] Use constructors for guessing struct member types
- [ ] Return type inference
- [x] Mutability based on usage

## Working Features

Only bare functions using the basic language features are supported. Some of them work partially.
- [x] classes
- [x] functions
- [x] lambdas
- [x] list comprehensions
- [ ] inheritance
- [ ] operator overloading
- [ ] function and class decorators
- [ ] getter/setter function decorators
- [ ] yield (generator functions)
- [ ] function calls with `*args` and `**kwargs`

Language Keywords
- [ ] global, nonlocal
- [x] while, for, continue, break
- [x] if, elif, else
- [x] try, except, raise
- [x] def, lambda
- [ ] new, class
- [x] from, import
- [ ] as
- [x] pass, assert
- [x] and, or, is, in, not
- [x] return
- [ ] yield

Builtins
- [ ] dict
- [x] list
- [ ] tuple
- [x] int
- [ ] float
- [x] str
- [ ] round
- [x] range
- [ ] range_step
- [ ] sum
- [x] len
- [x] map
- [x] filter

Data Structures
- [x] list
- [ ] Set
- [x] String
- [ ] Dict
