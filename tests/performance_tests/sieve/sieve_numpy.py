import sys
import numpy as np
# Thanks to https://stackoverflow.com/questions/49936222/an-efficient-sieve-of-eratosthenes-in-python
# for the optimizations to sieve

def sieve(n):
    primes = np.ones(n, dtype=bool)
    primes[0], primes[1] = False, False
    for i in range(2, int(np.sqrt(n) + 1)):
        if primes[i]:
            # Vectorization of the assignment operation (Uses a loop in C)
            primes[i*i::i] = False 
    return np.flatnonzero(primes)

if __name__ == "__main__":
    sieve(int(sys.argv[1]))