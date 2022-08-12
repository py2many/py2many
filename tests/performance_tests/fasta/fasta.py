# The Computer Language Benchmarks Game
# https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
#
# modified by Ian Osgood
# modified again by Heinrich Acker
# modified by Justin Peel
# 2to3

import sys, bisect

alu = (
    "GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGG"
    "GAGGCCGAGGCGGGCGGATCACCTGAGGTCAGGAGTTCGAGA"
    "CCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAAT"
    "ACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCA"
    "GCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGG"
    "AGGCGGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCC"
    "AGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA"
)

iub = list(zip("acgtBDHKMNRSVWY", [0.27, 0.12, 0.12, 0.27] + [0.02] * 11))

homosapiens = [
    ("a", 0.3029549426680),
    ("c", 0.1979883004921),
    ("g", 0.1975473066391),
    ("t", 0.3015094502008),
]


def genRandom(ia=3877, ic=29573, im=139968):
    seed = 42
    imf = float(im)
    while 1:
        seed = (seed * ia + ic) % im
        yield seed / imf


Random = genRandom()


def make_cumulative(table: list[tuple[str, float]]):
    P = []
    C = []
    prob = 0.0
    for char, p in table:
        prob += p
        P += [prob]
        C += [char]
    return (P, C)


def repeatFasta(src: str, n: int):
    width = 60
    r = len(src)
    s = src + src + src[: n % r]
    for j in range(n // width):
        i = j * width % r
        print(s[i : i + width])
    if n % width:
        print(s[-(n % width) :])


def randomFasta(table, n: int):
    width = 60
    r = range(width)
    gR = Random.__next__
    bb = bisect.bisect
    jn = "".join
    probs, chars = make_cumulative(table)
    for j in range(n // width):
        x = jn([chars[bb(probs, gR())] for i in r])
        print(x)
    if n % width:
        print(jn([chars[bb(probs, gR())] for i in range(n % width)]))


def main():
    n = int(sys.argv[1])

    print(">ONE Homo sapiens alu")
    repeatFasta(alu, n * 2)

    print(">TWO IUB ambiguity codes")
    randomFasta(iub, n * 3)

    print(">THREE Homo sapiens frequency")
    randomFasta(homosapiens, n * 5)


main()
