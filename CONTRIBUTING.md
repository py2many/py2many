# Contributing

So you found a bug, fixed it and would like us to include it in the next release. If so, please
read-on.

## Outline

- [Generic docs on github pull requests](https://docs.github.com/en/github/collaborating-with-pull-requests/proposing-changes-to-your-work-with-pull-requests/about-pull-requests)
- Setting up your machine for testing
- Running tests locally
- Running tests via continuous integration (CI) pipeline

## Running tests using act

[This](https://github.com/adsharma/py2many/blob/main/.github/workflows/main.yml) is how CI pipleine does it.

This CI pipeline can be run locally using https://github.com/nektos/act which will use Docker
to run the GitHub Actions workflow.

On your first invocation of `act`, select the "Medium" runner image, as the workflow has been tested using that.
Refer to https://github.com/nektos/act#runners for more information.

As it installs many large dependencies, languages and packages, be sure to use `act --reuse --job build`
to reuse the same container for each invocation.

## Setting up your Ubuntu machine

Here are some notes for ubuntu 20.04

### Ubuntu 20.04 + python3

```bash
sudo apt install python3 python3-pip python3-pytest tox black flake8
```

### Ubuntu 20.04 + C++

```bash
sudo apt install clang-format clang++ libc++-dev libc++abi-dev
```

### Ubuntu 20.04 + Rust

- Follow https://rustup.rs/

```bash
rustup install nightly
rustup component add --toolchain nightly clippy
rustup component add --toolchain nightly rustfmt
```

## MacOS dependencies

The following commands will install most of the dependencies on MacOS

```bash
brew install astyle clang-format flutter gcc go julia kotlin maven nim rust vlang z3
```

## Setting up python dependencies
```bash
pip3 install -e .[test]
```

## Running tests for C++ only

```bash
pytest-3 -k cpp -v
```

Other languages will be similar.

## Updating expected output

Most test cases live in `<repo>/tests/cases/*.py` and the expected output after
transpilation are in `<repo>/tests/expected`. If you make changes to any of the
tests, follow the recipe below and inspect the updated files in `tests/expected`.

```bash
export UPDATE_EXPECTED=1
pytest-3 -k cli -v
```

When tests are run, temporary files are generated, compared against expected
golden output and then discarded. If you want to keep them around for debugging
purposes, you can use:

```bash
export KEEP_GENERATED=1
pytest-3 -k some_test -v
```

## Running tests via CI

- Submit your pull request (PR) using the process outlined above
- Navigate to your [pull request](https://github.com/adsharma/py2many/pulls)
- First time committers require their PRs to be approved for CI
- Once approved (automatic on your second PR), you'll see a list of jobs at the
  bottom of the page. Once all tests pass, your PR is ready to be reviewed for
  merging.
