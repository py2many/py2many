# The Computer Language Benchmarks Game
# https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
#
# submitted by Joerg Baumann

from bisect import bisect
from contextlib import closing, contextmanager
from itertools import accumulate, chain, islice, zip_longest
from multiprocessing import Lock, RawValue, Process
from os import cpu_count
from re import sub
from sys import argv, stdout

write = stdout.buffer.write

def acquired_lock():
    lock = Lock()
    lock.acquire()
    return lock

def started_process(target, args):
    process = Process(target=target, args=args)
    process.start()
    return process

@contextmanager
def lock_pair(pre_lock=None, post_lock=None, locks=None):
    pre, post = locks if locks else (pre_lock, post_lock)
    if pre:
        pre.acquire()
    yield
    if post:
        post.release()

def write_lines(
        sequence, n, width, lines_per_block=10000, newline=b'\n', table=None):
    i = 0
    blocks = (n - width) // width // lines_per_block
    if blocks:
        for _ in range(blocks):
            output = bytearray()
            for i in range(i, i + width * lines_per_block, width):
                output += sequence[i:i + width] + newline
            else:
                i += width
            if table:
                write(output.translate(table))
            else:
                write(output)

    output = bytearray()
    if i < n - width:
        for i in range(i, n - width, width):
            output += sequence[i:i + width] + newline
        else:
            i += width
    output += sequence[i:n] + newline
    if table:
        write(output.translate(table))
    else:
        write(output)
    stdout.buffer.flush()

def cumulative_probabilities(alphabet, factor=1.0):
    probabilities = tuple(accumulate(p * factor for _, p in alphabet))

    table = bytearray.maketrans(
                bytes(chain(range(len(alphabet)), [255])),
                bytes(chain((ord(c) for c, _ in alphabet), [10]))
            )

    return probabilities, table

def copy_from_sequence(header, sequence, n, width, locks=None):
    sequence = bytearray(sequence, encoding='utf8')
    while len(sequence) < n:
        sequence.extend(sequence)

    with lock_pair(locks=locks):
        write(header)
        write_lines(sequence, n, width)

def lcg(seed, im, ia, ic):
    local_seed = seed.value
    try:
        while True:
            local_seed = (local_seed * ia + ic) % im
            yield local_seed
    finally:
        seed.value = local_seed

def lookup(probabilities, values):
    for value in values:
        yield bisect(probabilities, value)

def lcg_lookup_slow(probabilities, seed, im, ia, ic):
    with closing(lcg(seed, im, ia, ic)) as prng:
        yield from lookup(probabilities, prng)

def lcg_lookup_fast(probabilities, seed, im, ia, ic):
    local_seed = seed.value
    try:
        while True:
            local_seed = (local_seed * ia + ic) % im
            yield bisect(probabilities, local_seed)
    finally:
        seed.value = local_seed

def lookup_and_write(
        header, probabilities, table, values, start, stop, width, locks=None):
    if isinstance(values, bytearray):
        output = values
    else:
        output = bytearray()
        output[:stop - start] = lookup(probabilities, values)

    with lock_pair(locks=locks):
        if start == 0:
            write(header)
        write_lines(output, len(output), width, newline=b'\xff', table=table)

def random_selection(header, alphabet, n, width, seed, locks=None):
    im = 139968.0
    ia = 3877.0
    ic = 29573.0

    probabilities, table = cumulative_probabilities(alphabet, im)

    if not locks:
        with closing(lcg_lookup_fast(probabilities, seed, im, ia, ic)) as prng:
            output = bytearray(islice(prng, n))

        lookup_and_write(header, probabilities, table, output, 0, n, width)
    else:
        pre_seed, post_seed, pre_write, post_write = locks

        m = cpu_count() * 3 if n > width * 15 else 1
        partitions = [n // (width * m) * width * i for i in range(1, m)]

        processes = []
        pre = pre_write

        with lock_pair(locks=(pre_seed, post_seed)):
            with closing(lcg(seed, im, ia, ic)) as prng:
                for start, stop in zip([0] + partitions, partitions + [n]):
                    values = list(islice(prng, stop - start))

                    post = acquired_lock() if stop < n else post_write

                    processes.append(started_process(
                        lookup_and_write,
                        (header, probabilities, table, values,
                         start, stop, width, (pre, post))
                    ))

                    pre = post

        for p in processes:
            p.join()

def fasta(n):
    alu = sub(r'\s+', '', """
GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGGGAGGCCGAGGCGGGCGGA
TCACCTGAGGTCAGGAGTTCGAGACCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACT
AAAAATACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCAGCTACTCGGGAG
GCTGAGGCAGGAGAATCGCTTGAACCCGGGAGGCGGAGGTTGCAGTGAGCCGAGATCGCG
CCACTGCACTCCAGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA
""")

    iub = list(zip_longest('acgtBDHKMNRSVWY',
                           (.27, .12, .12, .27), fillvalue=.02))

    homosapiens = list(zip('acgt', (0.3029549426680, 0.1979883004921,
                                    0.1975473066391, 0.3015094502008)))

    seed = RawValue('f', 42)
    width = 60
    tasks = [
        (copy_from_sequence,
         [b'>ONE Homo sapiens alu\n', alu, n * 2, width]),
        (random_selection,
         [b'>TWO IUB ambiguity codes\n', iub, n * 3, width, seed]),
        (random_selection,
         [b'>THREE Homo sapiens frequency\n', homosapiens, n * 5, width, seed]),
    ]

    if cpu_count() < 2:
        for func, args in tasks:
            func(*args)
    else:
        written_1 = acquired_lock()
        seeded_2 = acquired_lock()
        written_2 = acquired_lock()

        locks_sets = [
            (None, written_1),
            (None, seeded_2, written_1, written_2),
            (seeded_2, None, written_2, None),
        ]

        processes = [
            started_process(target, args + [locks_sets[i]])
                for i, (target, args) in enumerate(tasks)
        ]

        for p in processes:
            p.join()

if __name__ == "__main__":
    fasta(int(argv[1]))
    