fn fib(i: Int64) -> Int64:
    if i == 0 or i == 1:
        return 1

    return fib((i - 1)) + fib((i - 2))


fn main():
    print(fib(5))
