import math
import sys

# @offset_arrays # For PyJL
def sieve(n: int):
    primes = [True] * (n)
    primes[0], primes[1] = False, False
    for i in range(2, int(math.sqrt(n) + 1)):
        if primes[i]:
            for j in range(i*i, n, i):
                primes[j] = False
    return list(filter(lambda j: primes[j], range(2,n)))

if __name__ == "__main__":
    sieve(int(sys.argv[1]))