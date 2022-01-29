def fib(n:int):
    a = 0
    b = 1
    for i in range(1,n):
      yield a
      a, b = b, a+b