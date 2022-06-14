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

```
sudo apt install python3 python3-pip python3-pytest tox black pyflakes3
```

### Ubuntu 20.04 + C++

```
sudo apt install clang-format clang++ libc++-dev libc++abi-dev
```

### Ubuntu 20.04 + Rust

- Follow https://rustup.rs/

```
rustup component add rustfmt
cargo install cargo-script
```

## MacOS dependencies

The following commands will install most of the dependencies on MacOS

```
brew tap holgerbrandl/tap https://github.com/holgerbrandl/homebrew-tap
brew tap sdkman/tap
brew install astyle clang-format cljstyle flutter gcc go julia kscript ktlint nim sdkman-cli vlang z3
cargo install cargo-script
```

`cljstyle` will refuse to run.  In a shell, type `open /usr/local/bin/`, locate `cljstyle`, and Open.
MacOS will inform that it was downloaded from the Internet and ask for confirmation.
Once confirmed, it will become usable.

## Running tests for C++ only

```
alias t=`pytest-3`
t -k cpp -v
```

Other languages will be similar


## Running basic coverage test for all languages

```
pytest-3 -k coverage -v
```

## Updating expected output

Most test cases live in `<repo>/tests/cases/*.py` and the expected output after
transpilation are in `<repo>/tests/expected`. If you make changes to any of the
tests, follow the recipe below and inspect the updated files in `tests/expected`.

```
export UPDATE_EXPECTED=1
t -k changed_tests_filter -v
```

When tests are run, temporary files are generated, compared against expected
golden output and then discarded. If you want to keep them around for debugging
purposes, you can use:

```
export KEEP_EXISTING=1
t -k some_test -v
```

## Running tests via CI

- Submit your pull request (PR) using the process outlined above
- Navigate to your [pull request](https://github.com/adsharma/py2many/pulls)
- First time committers require their PRs to be approved for CI
- Once approved (automatic on your second PR), you'll see a list of jobs at the
  bottom of the page. Once all tests pass, your PR is ready to be reviewed for
  merging.
