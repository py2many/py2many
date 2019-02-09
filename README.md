# Python to Rust transpiler

This project is not aimed at producing ready-to-compile code, but can be used as a starting point for porting Python project to Rust.

It generates unidiomatic non-optimized code with lots of unnecessary allocations, but can reduce amount of typing needed.

On the other hand, some Python features like tuples and slices lay out nicely when transpiling.

Only small subset of Python is supported right now and the end goal is to support common cases at least as a placeholders.

Based on Lukas Martinelli [Py14](https://github.com/lukasmartinelli/py14) and [Py14/python-3](https://github.com/ProgVal/py14/tree/python-3) branch by Valentin Lorentz.

## Example

Original Python version.

```python
if __name__ == "__main__":
    things = ["Apple", "Banana", "Dog"]
    animals = []
    for thing in things:
        if thing == "Dog":
            animals.append(thing)
    
    print(animals)
```

Transpiled Rust code.


```rust
use std::*;

fn main() {
    let mut things = vec!["Apple", "Banana", "Dog"];
    let mut animals = vec![];
    for thing in things {
        if thing == "Dog" {
            animals.push(thing);
        }
    }
    println!("{:?}", animals);
}

```

## Trying it out

Requirements:
- python 3
- rustc

Transpiling:

```
./pyrs.py test.py > test.rs
```

Formatting(optional):

```
rustfmt test.rs
```

Compiling:

```
rustc test.rs
```


## Working Features

Only bare functions using the basic language features are supported.

- [x] classes
- [x] functions
- [x] lambdas
- [ ] multiple inheritance
- [ ] operator overloading
- [ ] function and class decorators
- [ ] getter/setter function decorators
- [ ] list comprehensions
- [ ] yield (generator functions)
- [ ] function calls with `*args` and `**kwargs`

Language Keywords

- [ ] global, nonlocal
- [x] while, for, continue, break
- [x] if, elif, else
- [ ] try, except, raise
- [x] def, lambda
- [ ] new, class
- [x] from, import, as
- [x] pass, assert
- [x] and, or, is, in, not
- [x] return
- [ ] yield

Builtins
- [ ] dir
- [ ] type
- [ ] hasattr
- [ ] getattr
- [ ] setattr
- [ ] issubclass
- [ ] isinstance
- [ ] dict
- [ ] list
- [ ] tuple
- [x] int
- [ ] float
- [x] str
- [ ] round
- [x] range
- [ ] sum
- [x] len
- [ ] map
- [ ] filter
- [ ] min
- [ ] max
- [ ] abs
- [ ] ord
- [ ] chr
- [ ] open

Data Structures

- [x] list
- [ ] Set
- [x] String
- [ ] Dict
