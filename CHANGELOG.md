# Changelog

## [0.4.0] - 2023-12-31

### Added

- Add [typpete](https://github.com/adsharma/Typpete) as a type inference engine.
  Use --typpete=1 to activate.
- Install transpilers under py2many to avoid conflicts with other PyPI packages.
- Kotlin formatting now depends on [jgo](https://pypi.org/project/jgo/) using branch
  `git+https://github.com/jayvdb/jgo@sort-jars`.
  If jgo is not installed, no formatting will occur.
- Add SMT support.
- Added support for finding c++ headers `range.hpp` and `catch_test_macros.hpp` using conan.

### Improved

- Many improvements for C++, Julia, and Vlang.
- Go: Replace custom dependency `github.com/adsharma/py2many/pygo/runtime` with
  `github.com/electrious/refutil`.
- Improved float support using crate `float-ord`.
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
