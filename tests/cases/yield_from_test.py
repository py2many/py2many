@resumable
def generator1():
    for i in range(3):
        yield i


@resumable
def generator2():
    for j in range(3, 5):
        yield j


@resumable(lower_yield_from=True)
def yield_from():
    yield from generator1()
    yield from generator2()
    # print(map)


if __name__ == "__main__":
    arr = []
    for i in yield_from():
        arr.append(i)
    assert arr == [0, 1, 2, 3, 4]
