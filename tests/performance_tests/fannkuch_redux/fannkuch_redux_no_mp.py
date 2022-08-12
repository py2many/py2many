# The Computer Language Benchmarks Game
# https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
#
# contributed by Joerg Baumann
# many thanks to Oleg Mazurov for his helpful description

from math import factorial
from multiprocessing import cpu_count, Pool
from itertools import islice, starmap
import sys


def permutations(n:int, start:int, size:int):
    p = bytearray(range(n))
    count = bytearray(n)

    remainder = start
    for v in range(n - 1, 0, -1):
        count[v], remainder = divmod(remainder, factorial(v))
        for _ in range(count[v]):
            p[:v], p[v] = p[1 : v + 1], p[0]

    assert count[1] == 0
    assert size < 2 or (size % 2 == 0)

    if size < 2:
        yield p[:]
    else:
        rotation_swaps = [None] * n
        for i in range(1, n):
            r = list(range(n))
            for v in range(1, i + 1):
                r[:v], r[v] = r[1 : v + 1], r[0]
            swaps = []
            for dst, src in enumerate(r):
                if dst != src:
                    swaps.append((dst, src))
            rotation_swaps[i] = tuple(swaps)

        while True:
            yield p[:]
            p[0], p[1] = p[1], p[0]
            yield p[:]
            i = 2
            while count[i] >= i:
                count[i] = 0
                i += 1
            else:
                count[i] += 1
                t = p[:]
                for dst, src in rotation_swaps[i]:
                    p[dst] = t[src]



def alternating_flips_generator(n:int, start:int, size:int):
    maximum_flips = 0
    alternating_factor = 1
    for permutation in islice(permutations(n, start, size), size):
        first = permutation[0]
        if first:
            flips_count = 1
            while True:
                permutation[: first + 1] = permutation[first::-1]
                first = permutation[0]
                if not first:
                    break
                flips_count += 1
            if maximum_flips < flips_count:
                maximum_flips = flips_count
            yield flips_count * alternating_factor
        else:
            yield 0
        alternating_factor = -alternating_factor
    yield maximum_flips


def task(n:int, start:int, size:int):
    alternating_flips = alternating_flips_generator(n, start, size)
    return (sum(islice(alternating_flips, size)), next(alternating_flips))


def fannkuch(n: int):
    if n < 0:
        for data in islice(permutations(-n, 0, factorial(-n)), factorial(-n)):
            print("".join(map(lambda n: str(n + 1), data)))
    else:
        assert n > 0

        task_size = factorial(n)

        # assert(task_size % 2 == 0)
        checksums, maximums = zip(task(n, 0, task_size))

        checksum, maximum = sum(checksums), max(maximums)
        print("{0}\nPfannkuchen({1}) = {2}".format(checksum, n, maximum))


if __name__ == "__main__":
    fannkuch(10)
    # fannkuch(int(sys.argv[1]))
