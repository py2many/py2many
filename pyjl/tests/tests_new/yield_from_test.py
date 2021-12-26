def generator1():
    for i in range(3):
        yield i

def generator():
    yield from generator1()
    yield from generator2()
    # print(map)

def generator2():
    for j in range(3, 5):
        yield j

if __name__=="__main__":
    arr = []
    for i in generator():
        arr.append(i)
    assert arr == [0,1,2,3,4]