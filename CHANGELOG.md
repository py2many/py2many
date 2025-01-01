# Changelog

## [0.6] - 2025-01-01

- Mojo backend
- Much improved type inference
- Python 3.13 supported
- Streamlined dependencies

## [0.5.1] - 2024-08-10

- Minor release eng related cleanups

## [0.5] - 2024-08-10

- Python 3.12 support
- Support GCC 13
- Fixed typpete support on Python 3.8
- Replace cargo-eval with cargo -Zscript.  This requires `nightly-2024-01-01`.
- Added clippy as Rust linter.
- Add Julia rewriter for boolean operations.
- Coverage increased from 89% to 92%,
  removing code in transpilers that emitted invalid code.
- Support D Programming Language
- Ubuntu 24.04 added to the test matrix
- Docker images usable now for testing several major languages

## [0.4.0] - 2023-12-31

### Added

- Added [typpete](https://github.com/adsharma/Typpete) as a type inference engine.
  Use --typpete=1 to activate.
- Transpilers are now located under py2many to avoid conflicts with other PyPI packages.
- Kotlin formatting now depends on [jgo](https://pypi.org/project/jgo/) using branch
  `git+https://github.com/jayvdb/jgo@sort-jars`.
  If jgo is not installed, no formatting will occur.
- New target: SMT transpiler of semi-Python syntax.  See `tests/cases/demorgan.py` as an example.
- Added support for finding c++ headers `range.hpp` and `catch_test_macros.hpp` using conan.
- Improved support for floats for all transpilers.
- pyv: Initial exception and class support.

### Improved

- Many improvements for C++, Julia, and Vlang.
- Go: Replace custom dependency `github.com/adsharma/py2many/pygo/runtime` with
  `github.com/electrious/refutil`.
- Improved Rust float support using crate `float-ord`.
- Find `format.jl` at runtime.

## [0.3.0] - 2021-07-14

### Added

- Internal: Migrate API translation code to plugin infra
- New target: python. Transpiles untyped python to typed python.
- New target: v. Transpiles python to [vlang](https://vlang.io)
- [Directory mode](https://github.com/adsharma/py2many/tree/main/tests/dir_cases). Cross module type inference.
- Support for sys.argv, sys.exit, target specific main() signature
- bitops, byte literals, min/max
- type inference: key and value types for dicts

### Improved

- Test coverage: up to 90%

### Rust

- Experimental: pyO3 extension for rust via --rust=1 --extension
- ADTs/Enums supported via python sealed classes implemented on top of [adt](https://github.com/jspahrsummers/adt) library
- Safe integer arithmetic only for widening ops. Details in [#123](https://github.com/adsharma/py2many/issues/123)
- [argparse](https://github.com/adsharma/py2many/blob/main/tests/expected/fib_with_argparse.rs) transpiled to structopt
- [stdio](https://github.com/adsharma/py2many/blob/main/tests/expected/with_open.rs): `with_open`, file read/write, text/binary, tmpfile
- Lifetimes: auto compute lifetimes for static strings
