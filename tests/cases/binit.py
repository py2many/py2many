from typing import List


def bisect_right(data: List[int], item: int) -> int:
    low = 0
    high = len(data)
    while low < high:
        middle = int((low + high) / 2)
        if item < data[middle]:
            high = middle
        else:
            low = middle + 1
    return low


def bin_it(limits: List[int], data: List[int]) -> List[int]:
    bins = [0]

    for x in limits:
        bins.append(0)

    for d in data:
        bins[bisect_right(limits, d)] += 1
    return bins
