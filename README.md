# The worlds poorest JIT compiler

Just add the `@cpp` to your function and on the next call the following will happen:

1. Python function is transpiled into C++ 14 template. This is possible through the `auto` return type of C++ 14 and extensive use of templates.
2. Type of the arguments to the functions are traced
3. C++ will be compiled for the traced types
4. Python bindings are generated with the help of [boost python](http://www.boost.org/doc/libs/1_57_0/libs/python/doc/index.html)
5. Call C++ version of function for subsequent calls

## How it works

Consider the worlds worst fibonacci implementation.

```python
import sys
from cppython import Cpp

@Cpp
def fib(n):
    if n == 1:
        return 1
    elif n == 0:
        return 0
    else:
        return fib(n-1) + fib(n-2)

if __name__ == "__main__":
    n = int(sys.argv[1])
    print(fib(n))
```

Generating the C++ code for a Python function does not require knowing
the types - as long as you generate a template.
The above `fib` function can be represented as a template.


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

When binding to the Python code we have to know the types of the parameters.
The `@cpp` decorator therefor records the types the function is called with and
generates and according binding.

```
BOOST_PYTHON_MODULE(fib_extern) {
    boost::python::def("fib", fib<int>);
}
```

## Trying it out

Because this requires [boost python](http://www.boost.org/doc/libs/1_57_0/libs/python/doc/index.html) and the newest version of clang it will be difficult to
get this to work on your machine.  I therefore recommend using Docker.

Build the provided dockerfile.

```
sudo docker build -t cppython .
```

And then run the sample `fib.py`

```
docker run -v $(pwd):/root cppython python fib.py 42
```


## In the future...

It should be possible to compile the C++ function for all the types
the function is called with. Consider the follwing `add` method.

```python
def add(a, b):
    return a + b

if __name__ == "__main__":
    print(add(10, 3))
    print(add("Hello", "World"))
```

On the first call to add we compile the method for integers and on the second call
for integers and strings.

```
BOOST_PYTHON_MODULE(fib_extern) {
    boost::python::def("fib_int", fib<int>);
    boost::python::def("fib_str", fib<std::string>);
}
```

The decorator chooses the right C++ method to call for you.


