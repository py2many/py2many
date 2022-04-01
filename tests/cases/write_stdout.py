
from sys import stdout

if __name__ == "__main__":
    write = stdout.buffer.write
    stdout.buffer.write(b"Test\n")
    write(b"P4\n")
    flush = stdout.buffer.flush
    stdout.buffer.flush