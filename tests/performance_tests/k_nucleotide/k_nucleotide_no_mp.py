# The Computer Language Benchmarks Game
# https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
#
# submitted by Joerg Baumann

from os import cpu_count
from sys import stdin
from collections import defaultdict
from itertools import starmap, chain

lean_buffer = {}

def lean_args(sequence, reading_frames, i, j):
    global lean_buffer

    lean_key = len(lean_buffer)
    lean_buffer[lean_key] = sequence
    return lean_key, reading_frames, i, j

class lean_call:
    def __init__(self, func):
        self.func = func

    def __call__(self, lean_key, reading_frames, i, j):
        global lean_buffer

        sequence = lean_buffer[lean_key]
        results = self.func(sequence, reading_frames, i, j)
        lean_results = []
        for frame, n, frequences in results:
            lean_frequences = defaultdict(int)
            for reading_frame, bits_list in reading_frames:
                if reading_frame == frame:
                    for bits in bits_list:
                        lean_frequences[bits] = frequences[bits]
            lean_results.append((frame, n, lean_frequences))
        return lean_results

def count_frequencies(sequence, reading_frames, i, j):
    frames = tuple(
        sorted([frame for frame,_ in reading_frames], reverse=True))
    frequences_mask_list = tuple(
        ((defaultdict(int), (1 << (2 * frame)) - 1) for frame in frames))
    frame = frames[0]
    frequences, mask = frequences_mask_list[0]
    short_frame_frequences = frequences_mask_list[1:]

    mono_nucleotides = []
    frame_tail = len(frames) - 1
    if frame_tail >= 0 and frames[frame_tail] == 1:
        freq = frequences_mask_list[frame_tail][0]
        worklist = sequence[i:j]
        len_before = len(worklist)
        while len_before > 0:
            n = worklist[0:1]
            worklist = worklist.translate(None, n)
            len_after = len(worklist)
            freq[n[0]] = len_before - len_after
            len_before = len_after
            mono_nucleotides.append(n)
        frame_tail -= 1

    if frame_tail >= 0 and frames[frame_tail] == 2 and mono_nucleotides:
        freq = frequences_mask_list[frame_tail][0]
        worklist = sequence[i:min(j+1, len(sequence))]
        overlaps = []
        for v in (n + m for n in mono_nucleotides for m in mono_nucleotides):
            bits = v[0]*4+v[1]
            freq[bits] = worklist.count(v)
            if v[1:] == v[:1]:
                overlaps.append((v, bits, v[:1]+v))
        for v, bits, pattern in overlaps:
            count = len(worklist)
            tmp = worklist.replace(pattern+pattern, b'12')
            tmp = tmp.replace(pattern, b'1')
            count = (count - len(tmp)) // 2
            count += tmp.count(b'1'+v)
            count += tmp.count(b'2'+v[:1])
            freq[bits] += count
        frame_tail -= 1

    short_frame_frequences = short_frame_frequences[:frame_tail]
    if len(short_frame_frequences):
        bits = 0
        if i == 0:
            for k in range(i, i + frame - 1):
                bits = bits * 4 + sequence[k]
                for t, (f, m) in enumerate(short_frame_frequences, 1):
                    if k - i + 1 >= frames[t]:
                        f[bits & m] += 1
        else:
            for k in range(i - frame + 1, i):
                bits = bits * 4 + sequence[k]

        for byte in sequence[k+1:j]:
            bits = (bits * 4 + byte) & mask
            frequences[bits] += 1
            for f, m in short_frame_frequences:
                f[bits & m] += 1

    return [
        (frame, len(sequence) - frame + 1, frequences_mask_list[i][0])
            for i, frame in enumerate(frames)]

def read_sequence(file, header, translation) :
    for line in file:
        if line[0] == ord('>'):
            if line[1:len(header)+1] == header:
                break

    sequence = bytearray()
    for line in file:
        if line[0] == ord('>'):
            break
        sequence += line

    return sequence.translate(translation, b'\n\r\t ')

def lookup_frequency(results, frame, bits):
    n = 1
    frequency = 0
    for _, n, frequencies in filter(lambda r: r[0] == frame, results):
        frequency += frequencies[bits]
    return frequency, n if n > 0 else 1

def display(results, display_list, sort=False, relative=False, end='\n'):
    lines = [
        (k_nucleotide, lookup_frequency(results, frame, bits))
            for k_nucleotide, frame, bits in display_list
    ]
    if sort: lines = sorted(lines, key=lambda v: (-v[1][0], v[0]))
    for k_nucleotide, (frequency, n) in lines:
        if relative:
            print("{0} {1:.3f}".format(k_nucleotide, frequency * 100. / n))
        else:
            print("{1}\t{0}".format(k_nucleotide, frequency))
    print(end=end)

def main():
    translation = bytes.maketrans(b'GTCAgtca',
        b'\x00\x01\x02\x03\x00\x01\x02\x03')
    def str_to_bits(text):
        buffer = text.encode('latin1').translate(translation)
        bits = 0
        for k in range(len(buffer)):
            bits = bits * 4 + buffer[k]
        return bits
    def display_list(k_nucleotides):
        return [(n, len(n), str_to_bits(n)) for n in k_nucleotides]

    sequence = read_sequence(stdin.buffer, b'THREE', translation)

    mono_nucleotides = ('G', 'A', 'T', 'C')
    di_nucleotides = tuple(n + m
        for n in mono_nucleotides for m in mono_nucleotides)
    k_nucleotides = (
        'GGT', 'GGTA', 'GGTATT', 'GGTATTTTAATT', 'GGTATTTTAATTTATAGT')

    reading_frames = [
        (1, tuple(map(str_to_bits, mono_nucleotides))),
        (2, tuple(map(str_to_bits, di_nucleotides))),
    ] + list(map(lambda s: (len(s), (str_to_bits(s),)), k_nucleotides))

    n = 1
    partitions = [len(sequence) * i // n for i in range(n+1)]
    count_jobs = [
        (sequence, reading_frames, partitions[i], partitions[i + 1])
            for i in range(len(partitions) - 1)]

    results = list(chain(*starmap(count_frequencies, count_jobs)))

    display(results, display_list(mono_nucleotides), relative=True, sort=True)
    display(results, display_list(di_nucleotides), relative=True, sort=True)
    display(results, display_list(k_nucleotides), end='')

if __name__=='__main__' :
    main()