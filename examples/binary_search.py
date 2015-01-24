#!/usr/bin/env python
def search(seq, key):
    lo = 0
    hi = len(seq) - 1
    while hi >= lo:
        mid = lo + (hi - lo) // 2
        if seq[mid] < key:
            lo = mid + 1
        elif seq[mid] > key:
            hi = mid - 1
        else:
            return mid
    return False #This will not work...

if __name__ == "__main__":
    seq = [1, 2, 5, 10, 11, 11, 12, 13, 17, 23]
    elem = search(seq, 12)
    if elem:
        print(elem)
