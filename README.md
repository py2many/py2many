# py2many: Python to Rust, C++, Go, Zig, Mojo & More - Universal Python Transpiler

![Build](https://github.com/py2many/py2many/actions/workflows/fast.yaml/badge.svg)
![License](https://img.shields.io/github/license/adsharma/py2many?color=brightgreen)

**Convert Python code to Rust, C++, Go, Zig, Julia, Nim, Dart, and other languages automatically**

py2many is a powerful Python transpiler that converts Python source code into multiple statically-typed programming languages. Transform your Python code to Rust for performance, C++ for systems programming, Go for concurrency, or Kotlin for mobile development.

## Why Convert Python to Other Languages

**Performance**: Python is popular and easy to program in, but has poor runtime
performance. Transpiling Python to Rust, C++, or Go can dramatically improve execution speed
while maintaining the development experience of Python.

**Security**: Writing security-sensitive code in low-level languages like C is error-prone and could
lead to privilege escalation. With py2many, you can write secure code in Python, verify it
with unit tests, then transpile to a safer systems language like Rust.

**Cross-platform Development**: Accelerate Python code by transpiling
it into native [extensions](https://github.com/adsharma/py2many/issues/62) or standalone applications.

**Mobile & Systems Programming**: While Swift and Kotlin dominate mobile app development,
there's no universal solution for sharing lower-level library code between platforms.
py2many provides an alternative to Kotlin Mobile Multiplatform (KMM) by letting you
write once in Python and deploy to multiple targets.

**Learning Tool**: It's an excellent educational tool for learning new programming languages
by comparing Python implementations with their transpiled equivalents.

## Supported Languages & Status

**Primary Focus**: **Python to Rust** conversion with the most mature feature set and active development.

**Production Ready**: **Python to C++** transpilation (C++14 historically supported, C++17+ required for advanced features).

**Beta Support**: Python to Julia, Python to Kotlin, Python to Nim, Python to Go, Python to Dart, Python to V, and Python to D transpilation.

**Type Inference**: py2many can also emit enhanced Python 3 code with inferred type annotations
and syntax improvements for better code analysis.

## Python to Rust Example

See how py2many converts Python code to idiomatic Rust:

**Original Python code:**

```python
def fib(i: int) -> int:
    if i == 0 or i == 1:
        return 1
    return fib(i - 1) + fib(i - 2)

# Demonstrate overflow handling
def add(i: i32, j: i32):
    return i + j
```

**Transpiled Rust code:**

```rust
fn fib(i: i32) -> i32 {
    if i == 0 || i == 1 {
        return 1;
    }
    return (fib((i - 1)) + fib((i - 2)));
}

// return type is i64
pub fn add(i: i32, j: i32) -> i64 {
    return ((i as i64) + (j as i64)) as i64;
}
```

**More Examples**: View transpiled code for all supported languages at:
https://github.com/adsharma/py2many/tree/main/tests/expected (fib*)

## Quick Start: Convert Python to Rust, C++, Go & More

**Requirements:**
- Python 3.8+

**Installation:**

```sh
pip3 install --user  # installs to $HOME/.local
```

OR

```sh
sudo pip3 install  # installs systemwide
```

**Usage Examples:**

Convert Python to different languages:

```sh
# Python to Rust
py2many --rust tests/cases/fib.py

# Python to C++
py2many --cpp tests/cases/fib.py

# Python to Go
py2many --go tests/cases/fib.py

# Python to Kotlin
py2many --kotlin tests/cases/fib.py

# Python to Julia
py2many --julia tests/cases/fib.py

# Python to Nim
py2many --nim tests/cases/fib.py

# Python to Dart
py2many --dart tests/cases/fib.py

# Python to D
py2many --dlang tests/cases/fib.py
```

**Compiling Transpiled Code:**

```sh
# Compile C++
clang tests/expected/fib.cpp

# Run Rust
./scripts/rust-runner.sh run tests/expected/fib.rs

# Run D
dmd -run tests/cases/fib.d
```

**Language-Specific Tools:**

py2many integrates with language-specific formatters and tools:
- `rustfmt` for Rust code formatting
- Language-specific standard libraries and external dependencies

For detailed setup instructions for each target language, see `.github/workflows/main.yml`.

## Key Features

- **Multi-Language Support**: Convert Python to 8+ programming languages
- **Type Inference**: Automatically infer and convert Python types to target language types
- **Performance Optimization**: Generate optimized code for systems programming languages
- **Cross-Platform**: Works on Linux, macOS, and Windows
- **Open Source**: MIT licensed with active community development
- **Educational**: Compare Python implementations with transpiled code to learn new languages

## Use Cases

- **Performance-Critical Applications**: Convert Python algorithms to Rust or C++ for speed
- **Systems Programming**: Transform Python prototypes to systems languages
- **Mobile Development**: Convert Python logic to Kotlin for Android development
- **WebAssembly**: Transpile Python to Rust for WASM deployment
- **Embedded Systems**: Convert Python code to C++ or Rust for resource-constrained environments
- **Cross-Platform Libraries**: Write once in Python, deploy to multiple language ecosystems

## Project History

Based on Julian Konchunas' [pyrs](http://github.com/konchunas/pyrs).

Based on Lukas Martinelli [Py14](https://github.com/lukasmartinelli/py14)
and [Py14/python-3](https://github.com/ProgVal/py14/tree/python-3) branch by Valentin
Lorentz.

# Contributing

See [CONTRIBUTING.md](https://github.com/adsharma/py2many/blob/main/CONTRIBUTING.md)
for how to test your changes and contribute to this project.
