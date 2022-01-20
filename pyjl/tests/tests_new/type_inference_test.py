
from typing import List


def fibonacci(n):
    if n == 0:
        return 0
    elif n == 1:
        return 1
    else:
        return fibonacci(n - 2) + fibonacci(n - 1)

def mul_list():
    a:list = []
    for i in range(0, 5):
        a.append(i)
    return 2*a 

def combinations(array):
    result = []
    for x in array:
        for y in array:
            result.append((x,y))
    return result


def mul_recvd_list(a, len):
    for i in range(0, len(a)):
        a.append(i)
    return 2*a 

if __name__ == "__main__":
    assert fibonacci(10) == 55
    assert fibonacci(3) * "ola" == "olaola"

    a = []
    a_mul = mul_recvd_list(a)
    print(a_mul)
    print("OK")
