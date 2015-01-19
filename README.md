# Python to C++ 14 transpiler
This is a little experiment that shows how far you can go with the C++ 14 `auto` return type and templates.
C++14 does type deduction so effectively that it is possible to transpile
Python into C++ without worrying about the dynamic nature of python.

## How it works

Consider the worlds worst fibonacci implementation.

```python
def fib(n):
    if n == 1:
        return 1
    elif n == 0:
        return 0
    else:
        return fib(n-1) + fib(n-2)
```

This can be translated into the following C++ template.

```c++
template <typename T1>
auto fib(T1 n) {
    if (n == 1) {
        return 1;
    } else if (n == 0) {
        return 0;
    } else {
        return fib(n-1) + fib(n-2);
    }
}
```

```python
def three_series(n):
    l = []
    for x in range(0, 10):
        l.append(3 * x)
    return l
```



#Getting rid yield

```python
def three_series(n):
    for x in range(0, 10):
        yield x
```

Now this code has to be transformed.

```python
def three_series(n):
    result = []
    for x in range(0, 10):
        result.append(3 * x)
    return result
```

In this sample we assume that `range` returns a C++ iterator
with begin and end.
So how do we specify the type of the vector l?
One way is to use `decltype` but because we don't know
x at that point in time.

We don't use auto inside a range-based loop because it makes looking up the
type harder.


```python
def fill():
    result = []
    val = 3 * 10
    result.append(10 * val)
    val = 4 * 10
    result.append(9 * val)
    return result
```

```python
def fill():
    val = 3 * 10
    result = [10 * val]
    val = 4 * 10
    result.append(9 * val)
    return result
```

```c++
template <typename T1>
auto three_series(T1 n) {
    auto range = range(0, 10);
    auto it = range.begin();
    auto result = make_from_pushback(3 * x);
    for(it; it != range.end(); ++it) {
        result.push_back(3 * x);
    }
    return result;
}
```

```c++
template <typename T1>
auto three_series(T1 n) {
    auto range = range(0, 10);
    auto it = range.begin();
    auto result = make_from_pushback(3 * x);
    for(it; it != range.end(); ++it) {
        result.push_back(3 * x);
    }
    return result;
}
```

or we just dont support returning containers..

```c++
template <typename T1>
auto three_series(T1 n) {
    using range_type = decltype(range(0, 10))::value_type;
    std::vector<?> result {};
    for(range_type x : range(0, 10)) {
        result.push_back(3 * x);
    }
    return result;
}
```

```c++
template <typename T1>
auto three_series(T1 n) {
    using range_type = decltype(range(0, 10))::value_type;
    using result_type = decltype(3 * std::declval<range_type>());
    std::vector<?> result {};
    for(range_type x : range(0, 10)) {
        result.push_back(3 * x);
    }
    return result;
}
```

## Specifying value types for containers

Let's look at a simple `map` implementation in pthon.

```python
def map(values, fun):
    return [fun(x) for x in values]

if __name__ == "__main__":
    values = [1, 2, 3, 4, 5]
    fun = lambda x: x * x
    results = map(values, fun)
```

If we translate this to C++ we don't know the `value_type` for
the `vector` (indicated with `?`).
The only place where types can be deduced from is the initializer list `{1, 2, 3, 4, 5}`.
The only types we have specified here are the contents

```c++
template <typename T1, typename T2>
auto map(T1 values, T2 fun) {
    std::vector<?> results {};
    for(auto x : values) {
        results.push_back(fun(x));
    }
    return results;
}

int main() {
    std::vector<?> values {1, 2, 3, 4, 5};
    auto fun = [](auto x) { return x * x; };
    auto results = map(values, fun);
}
```

We assume that the value_type of the list is the type of the first
inserted value `1`.
To get that type we can use `decltype`.

```
using value_type = decltype(1);
std::vector<value_type> values {1, 2, 3, 4, 5};
```

Now for the map function it is a bit trickier.
The first time something is inserted into the results container
is inside the for loop.
Because we now this will be transformed to a range based loop we know
that x has the same type as the `value_type` of the values container.

```c++
template <typename T1, typename T2>
auto map(T1 values, T2 fun) {
    using value_type = typename decltype(values)::value_type;
    std::vector<?> results {};
    for(value_type x : values) {
        results.push_back(fun(x));
    }
    return results;
}
```

We still don't know the types inside the results container. For this we
have to find out the type returned by `fun`.

```c++
template <typename T1, typename T2>
auto map(T1 values, T2 fun) {
    using value_type = typename decltype(values)::value_type;
    using return_type = decltype(fun(std::declval<value_type>()));
    std::vector<return_type> results {};
    for(value_type x : values) {
        results.push_back(fun(x));
    }
    return results;
}

int main():
    using value_type = decltype(1);
    std::vector<value_type> values{1, 2, 3, 4, 5};
    auto fun = [](auto x) { return x * x; };
    auto results = map(values, fun);
```


## Transpiling

TODO

## Application as the worlds poorest JIT compiler for Python

Just add the `@cpp` to your Python function and on the next call the following will happen:

1. Python function is transpiled into C++ 14 template.
2. Types of the arguments the function is being called with are traced.
3. C++ will be compiled for the traced types
4. Python bindings are generated with the help of [boost python](http://www.boost.org/doc/libs/1_57_0/libs/python/doc/index.html)
5. On subsequent calls the C++ version of the function is called


The only time we have to know the types is when we are compiling and binding to the Python code.
The `@cpp` decorator therefore records the types the function is called with and
generates the suitable bindings.

```c++
BOOST_PYTHON_MODULE(fib_extern) {
    boost::python::def("fib", fib<int>);
}
```

## Trying it out

Requirements:

- [boost python 1.55](http://www.boost.org/doc/libs/1_57_0/libs/python/doc/index.html)
- clang 3.5
- clang-format 3.5

It will be difficult to get this to work on your machine.
I therefore recommend using Docker.

Pull the docker image.

```
docker pull lukasmartinelli/poorjit
```

Or build the provided `Dockerfile`.

```
sudo docker build -t poorjit .
```

And then run the sample `fib.py`.

```
docker run -v $(pwd):/root poorjit python fib.py 42
```

## In the future...

It should be possible to compile the C++ function for all the types
the function is called with. Consider the following `add` method.

```python
def add(a, b):
    return a + b

if __name__ == "__main__":
    print(add(10, 3))
    print(add("Hello", "World"))
```

On the first call to `add` we compile the method for `int` and on the second call
a version for `int` and `str`.

```
BOOST_PYTHON_MODULE(fib_extern) {
    boost::python::def("fib_int", fib<int>);
    boost::python::def("fib_str", fib<std::string>);
}
```

The decorator then chooses the right C++ method to call for you.

## Type mapping

Type mapping only happens when Python needs to call C++ and back.
Only four basic types are supported and everything is passed by value in
order to stay sane.

Python   | C++
---------|-------------
bool     | bool
int      | int
str      | std::string
list     | std::vector
tuple    | std::tuple

When an argument or return value in python seems to be list
we dig deeper to check what types are in that list.

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
```

Knowing that we need to add dog to the struct we can only know by type
recording.

```c++
template <typename T1, typename T2, typename T3>
struct Person {
    T1 prename;
    T2 name;
    T3 dog;
    auto full_name() {
        return self.prename + " " + self.name;
    }
    void give_dog(T3 dog) {
        this.dog = dog;
    }
};
```
