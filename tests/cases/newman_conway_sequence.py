""" Python program to find the n-th element of
    Newman-Conway Sequence"""


def newman_conway_sequence(n: int):
    f = [0, 1, 1]
    for i in range(3, n + 1):
        r = f[f[i - 1]] + f[i - f[i - 1]]
        f.append(r)
    return r


if __name__ == "__main__":
    assert newman_conway_sequence(10) == 6
    assert newman_conway_sequence(30) == 16
    assert newman_conway_sequence(1000) == 510
