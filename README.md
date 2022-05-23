# py2many: Python to many CLike languages transpiler

![Build](https://github.com/adsharma/py2many/actions/workflows/main.yml/badge.svg)
![License](https://img.shields.io/github/license/adsharma/py2many?color=brightgreen)

## Why

Python is popular, easy to program in, but has poor runtime
performance. We can fix that by transpiling a subset of the language
into a more performant, statically typed language.

A second benefit is security. Writing security sensitive
code in a low level language like C is error prone and could
lead to privilege escalation. Specialized languages such as
[wuffs](https://github.com/google/wuffs) exist to address this use
case. py2many can be a more general purpose solution to the problem
where you can verify the source via unit tests before you transpile.

A third potential use case is to accelerate python code by transpiling
it into an [extension](https://github.com/adsharma/py2many/issues/62)

Swift and Kotlin dominate the mobile app development workflow. However, there is
no one solution that works well for lower level libraries where there is desire
to share code between platforms. Kotlin Mobile Multiplatform (KMM) is a player
in this place, but it hasn't really caught on. py2many provides an alternative.

Lastly, it's a great educational tool to learn a new language by implementing
a backend for your favorite language.

## Status

Rust is the language where the focus of development has been. C++14 is historically
the first language to be supported.

Preliminary support exists for Julia, Kotlin, Nim, Go and Dart.

py2many can also emit Python 3 code that includes inferred type annotations,
and revisions to the syntax intended to simplify parsing of the code.

## History

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

Transpiled Rust code:

```rust
fn fib(i: i32) -> i32 {
    if i == 0 || i == 1 {
        return 1;
    }
    return (fib((i - 1)) + fib((i - 2)));
}
```

Transpiled code for other languages:

https://github.com/adsharma/py2many/tree/main/tests/expected (fib*)


## Trying it out
### Local installation

**Windows**
```
setup.py install --user  # installs to $HOME/.local
```

OR

**Linux**
```
sudo ./setup.py install  # installs systemwide
```

### Transpiling
To run Py2Many, you can use the following command
```
py2many --<lang>=1 <path> [--outdir=<out_path>] [--indent=<indent_val>] [--comment-unsupported=<True|False>] [--extension=<True|False>] [--suffix=<suffix_val>] [--force=<True|False>] [--typpete=<True|False>] [--project=<True|False>] [--expected=<exp_path>] [--config=<config_path>]
```
- __lang__: The language we want to use (See examples in section below)
- __path__: Is either a path to a Python module or a folder containing Python modules.
- __outdir__: Where to output the transpiled results. If this is not specified when __path__ is a folder, py2many will create a new folder with the name of the original folder and add the suffix `-py2many`. The default is `None`
- __indent__: Indentation to use in languages that care. The default is `None`
- __comment-unsupported__: Place unsupported constructs in comments. The default is `False`
- __extension__: Build a python extension. The default is `False`
- __suffix__: Alternate suffix to use instead of the default one for the language. The default is `None`
- __force__: When output and input are the same file, force overwriting. The default is `False`
- __typpete__: Use typpete for inference. The default is `False`
- __project__: Create a project when using directory mode. The default is `True`
- __expected__: Location of output files to compare. Can either be a directory containing the expected file or a file. The file must have the same name as the input file.
- __config__: Input configuration files for the transpiler. They can be used to add external annotations to the Python source code or inject flags for the transpiler

### Configuration files
We provide the layout of a possible configuration file below:
```
[DEFAULT]
<default_param> = <val>

[FLAGS]
<flag> = True | False

[ANNOTATIONS]
<annotation_file_name>.yaml
```

### Dependencies
Please install the following dependencies before running Py2Many:
```
pip install toposort
pip install numpy
```

### Example
Add the py2many script to your $PATH and run:

```
py2many --cpp=1 /tmp/fib.py
py2many --rust=1 /tmp/fib.py
py2many --julia=1 /tmp/fib.py
py2many --kotlin=1 /tmp/fib.py
py2many --nim=1 /tmp/fib.py
py2many --dart=1 /tmp/fib.py
py2many --go=1 /tmp/fib.py
```

Compiling:

```
clang fib.cpp
rustc fib.rs
...
```

## Requirements:
- python 3
- clang
- rustc



# Contributing

See [CONTRIBUTING.md](https://github.com/adsharma/py2many/blob/main/CONTRIBUTING.md)
for how to test your changes and contribute to this project.
