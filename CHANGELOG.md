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
