# Python to C++ 14 transpiler
[![Wercker Status](https://img.shields.io/wercker/ci/54c7dd9680c707522500363b.svg?style=flat)](https://app.wercker.com/project/bykey/faee5da9a0f6981723b39973d3137158)
[![Coverage Status](https://coveralls.io/repos/lukasmartinelli/py14/badge.svg?branch=master)](https://coveralls.io/r/lukasmartinelli/py14?branch=master)
[![Scrutinizer Code Quality](https://img.shields.io/scrutinizer/g/lukasmartinelli/py14.svg?style=flat)](https://scrutinizer-ci.com/g/lukasmartinelli/py14/?branch=master)
[![Code Health](https://landscape.io/github/lukasmartinelli/py14/master/landscape.svg?style=flat)](https://landscape.io/github/lukasmartinelli/py14/master)

This is a little experiment that shows how far you can go with the
C++ 14 `auto` return type and templates.

C++14 has such powerful type deduction that it is possible to transpile
Python into C++ without worrying about the missing type annotations in python.

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


One might support simple structures like this Python class.

```python
class Person:
    def __init__(self, prename, name):
        self.prename = prename
        self.name = name

    def full_name(self):
        return self.prename + " " + self.name

    def give_dog(self, dog):
        self.dog = dog

if __name__ == "__main__":
    person = Person("Lukas", "Martinelli", "Bello")
    person.give_dog("Hasso")
    print(person.full_name())
```

We need to create a wrapper `makePerson` to parametrize the Person class.

```c++
template <typename T1, typename T2, typename T3>
struct Person {
    T1 prename;
    T2 name;
    T3 dog;
    auto full_name() { return this->prename + " "s + this->name; }
    void give_dog(T3 dog) { this->dog = dog; }
};
template <typename T1, typename T2, typename T3>
auto makePerson(T1 prename, T2 name, T3 dog) {
    return Person<T1, T2, T3>{prename, name, dog};
}

int main() {
    auto person = makePerson("Lukas"s, "Martinelli"s, "Bello"s);
    person.give_dog("Hasso");
    std::cout << person.full_name() << std::endl;
}
```
