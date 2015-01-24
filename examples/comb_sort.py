#!/ usr / bin / env python
def sort(seq):
    gap = len(seq)
    swap = True
    while gap > 1 or swap:
        gap = max(1, int(gap / 1.25))
        swap = False
        for i in range(len(seq) - gap):
            if seq[i] > seq[i + gap]:
                seq[i], seq[i + gap] = seq[i + gap], seq[i]
                swap = True
                return seq


if __name__ == "__main__":
    unsorted = [10, 6, 1, 0, 2, 3, 5, 1, 6, 2]
    sorted = sort(unsorted)
    for n in sorted:
        print(n)
