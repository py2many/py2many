#!/usr/bin/env python
def sort(seq):
    L = len(seq)
    for _ in range(L):
        for n in range(1, L):
            if seq[n] < seq[n - 1]:
                # Tuples not yet supported
                temp = seq[n - 1]
                seq[n - 1] = seq[n]
                seq[n] = temp
    return seq


if __name__ == "__main__":
    unsorted = [10, 6, 1, 0, 2, 3, 5, 1, 6, 2]
    sorted = sort(unsorted)
    for n in sorted:
        print(n)
