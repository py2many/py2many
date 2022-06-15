# The Computer Language Benchmarks Game
# https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
#
# contributed by Matt Vollrath

from sys import stdout


COMPLEMENTS = bytes.maketrans(
    b"ACGTUMRWSYKVHDBNacgtumrwsykvhdbn", b"TGCAAKYWSRMBDHVNTGCAAKYWSRMBDHVN"
)
COMMENT = ord(">")


def reverse_sequence(sequence):
    chunk = bytearray()
    complemented = sequence.translate(COMPLEMENTS, b"\n")
    seq_len = len(complemented)
    last_line_len = seq_len % 60
    if last_line_len:
        chunk += b"\n" + complemented[:last_line_len]
    for i in range(last_line_len, seq_len, 60):
        chunk += b"\n" + complemented[i : i + 60]
    return chunk[::-1]


def generate_sequences(lines):
    heading = None
    sequence = bytearray()
    for line in lines:
        if line[0] == COMMENT:
            if heading:
                yield heading, sequence
                sequence = bytearray()
            heading = line
        else:
            sequence += line
    yield heading, sequence


if __name__ == "__main__":
    stdin = open(0, buffering=1)

    for heading, sequence in generate_sequences(stdin.buffer):
        stdout.buffer.write(heading)
        stdout.buffer.write(reverse_sequence(sequence))
        stdout.buffer.flush()
