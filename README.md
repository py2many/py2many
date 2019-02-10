# Python to Rust transpiler

This project started as Python to Rust syntax converter. It is not aimed at producing ready-to-compile code, but some basic stuff can be compiled easily (see Examples).

It generates unidiomatic non-optimized code with unnecessary allocations, but can reduce amount of edits you have to do when porting Python projects.

Only basic subset of Python is supported right now and the end goal is to support common cases at least as a placeholders.

The project is in experimental, so it may crash or silently skip some statements, so be careful.

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
python3 ./pyrs.py test.py > test.rs
```

Formatting(optional):

```
rustfmt test.rs
```

Compiling:

```
rustc test.rs
```

## Using in directory mode

It is possible to convert whole directory recursively. It won't throw exception if some files cannot be converted. The following command will create `projectname-pyrs` folder alonside your project directory. Relative path is also supported. This mode invokes `rustfmt` automatically for every file.

```
python3 ./pyrs.py /home/user/projectname
```

## More examples

```python
if __name__ == "__main__":
   numbers = [1,5,10]
   multiplied = list(map(lambda num: num*3, numbers))
   
   comprehended = [n - 5 for n in multiplied if n != 3]

   print("result is", comprehended)
```
Transpiles to
```rust
fn main() {
    let mut numbers = vec![1, 5, 10];
    let multiplied = numbers.iter().map(|num| num * 3).collect::<Vec<_>>();
    let comprehended = multiplied
        .iter()
        .cloned()
        .filter(|&n| n != 3)
        .map(|n| n - 5)
        .collect::<Vec<_>>();
    println!("{:?} {:?} ", "result is", comprehended);
}
```

## Classes
```python
from chain.block import Block

class Genesis(Block):
    def __init__(self, creation_time):
        self.timestamp = creation_time
        self.prev_hashes = []
        self.precalculated_genesis_hash = Block.get_hash(self)
    
    def get_hash(self):
          return self.precalculated_genesis_hash
```

Will yield

```rust
use chain::block::Block;

struct Genesis {
    timestamp: ST0,
    prev_hashes: ST1,
    precalculated_genesis_hash: ST2,
}

impl Genesis {
    fn __init__<T0>(&self, creation_time: T0) {
        self.timestamp = creation_time;
        self.prev_hashes = vec![];
        self.precalculated_genesis_hash = Block::get_hash(self);
    }
    fn get_hash<RT>(&self) -> RT {
        return self.precalculated_genesis_hash;
    }
}
```

This one won't compile. All unknown types are labeled. T stands for Type, RT is for Return Type and ST is for Struct Type. Ordering them this way enables you finding and replacing them in the future.

Also Python 3.5 type hints inside function declaration can be transpiled:
```python
def cut(apple: Fruit, knife: Tool) -> Slice:
```


```rust
fn cut(apple: Fruit, knife: Tool) -> Slice {
```

## Todo list

- [ ] Type infering for struct declaration
- [ ] Return type infering
- [ ] Mutability based on usage

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
