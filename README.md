# Python to C++ 14 transpiler
[![Wercker Status](https://img.shields.io/wercker/ci/54c7dd9680c707522500363b.svg?style=flat)](https://app.wercker.com/project/bykey/faee5da9a0f6981723b39973d3137158)
[![Coverage Status](https://coveralls.io/repos/lukasmartinelli/py14/badge.svg?branch=master)](https://coveralls.io/r/lukasmartinelli/py14?branch=master)
[![Scrutinizer Code Quality](https://img.shields.io/scrutinizer/g/lukasmartinelli/py14.svg?style=flat)](https://scrutinizer-ci.com/g/lukasmartinelli/py14/?branch=master)
[![Code Health](https://landscape.io/github/lukasmartinelli/py14/master/landscape.svg?style=flat)](https://landscape.io/github/lukasmartinelli/py14/master)
[![Dependency Status](https://gemnasium.com/lukasmartinelli/py14.svg)](https://gemnasium.com/lukasmartinelli/py14)

Try it out online: http://py14.lukasmartinelli.ch/

This is a little experiment that shows how far you can go with the
C++ 14 `auto` return type and templates.
C++14 has such powerful type deduction that it is possible to transpile
Python into C++ without worrying about the missing type annotations in python.

## Example

Original Python version.

```python
def factorial(num):
    if num <= 1:
        return num
    return factorial(num-1) * num
```

Transpiled C++ template.


```c++
template <typename T1> auto factorial(T1 num) {
  if (num <= 1) {
    return num;
  }
  return factorial(num - 1) * num;
}
```

## How it works

Consider a `map` implementation.

```python
def map(values, fun):
    results = []
    for v in values:
        results.append(fun(v))
    return results
```

This can be transpiled into the following C++ template.

```c++
template <typename T1, typename T2>
auto map(T1 values, T2 fun) {
    std::vector<decltype(
        fun(std::declval<typename decltype(values)::value_type>()))> results{};
    for (auto v : values) {
        results.push_back(fun(v));
    }
    return results;
}
```

The parameters and the return types are deduced automatically
In order to define the results vector we need to:

1. Deduce the type for v returned from the values range
   `using v_type = typename decltype(values)::value_type`
2. Deduce the return type of `fun` for call with parameter v
   `decltype(fun(v))`
3. Because we dont know v at the time of definition we need to fake it
   `std::declval<v_type>()`
4. This results in the fully specified value type of the results vector
   `decltype(fun(std::declval<typename decltype(values)::value_type>()))`

## Trying it out

Requirements:

- clang 3.5

Transpiling:

```
./py14.py fib.py > fib.cpp
```

Compiling:

```
clang++ -Wall -Wextra -std=c++14 -Ipy14/runtime fib.cpp
```
Run regression tests:

```
cd regtests
make
```

Run tests

```
pip install -r requirements.txt
py.test --cov=py14
```

## More Examples

**Probability Density Function (PDF)**

```python
def pdf(x, mean, std_dev):
    term1 = 1.0 / ((2 * math.pi) ** 0.5)
    term2 = (math.e ** (-1.0 * (x-mean) ** 2.0 / 2.0 * (std_dev ** 2.0)))
    return term1 * term2
```

```c++
template <typename T1, typename T2, typename T3>
auto pdf(T1 x, T2 mean, T3 std_dev) {
  auto term1 = 1.0 / std::pow(2 * py14::math::pi, 0.5);
  auto term2 = std::pow(py14::math::e, -1.0 * std::pow(x - mean, 2.0) / 2.0 *
                                           std::pow(std_dev, 2.0));
  return term1 * term2;
}
```

**Fibonacci**

```python
def fib(n):
    if n == 1:
        return 1
    elif n == 0:
        return 0
    else:
        return fib(n-1) + fib(n-2)
```

```c++
template <typename T1> auto fib(T1 n) {
  if (n == 1) {
    return 1;
  } else {
    if (n == 0) {
      return 0;
    } else {
      return fib(n - 1) + fib(n - 2);
    }
  }
}
```

**Bubble Sort**

```python
def sort(seq):
    L = len(seq)
    for _ in range(L):
        for n in range(1, L):
            if seq[n] < seq[n - 1]:
                seq[n - 1], seq[n] = seq[n], seq[n - 1]
    return seq
```

```c++
template <typename T1> auto sort(T1 seq) {
  auto L = seq.size();
  for (auto _ : rangepp::range(L)) {
    for (auto n : rangepp::range(1, L)) {
      if (seq[n] < seq[n - 1]) {
        std::tie(seq[n - 1], seq[n]) = std::make_tuple(seq[n], seq[n - 1]);
      }
    }
  }
  return seq;
}
```

## Working Features

Only bare functions using the basic language features are supported.

- [ ] classes
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
- [ ] pass, assert
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
