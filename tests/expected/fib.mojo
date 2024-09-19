fn fib(i: Int) -> Int:
    if i == 0 or i == 1:
        return 1

    return fib((i - 1)) + fib((i - 2))


fn main():
    print(fib(5))
