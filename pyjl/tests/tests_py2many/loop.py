def for_with_break():
    arr = []
    for i in range(4):
        if i == 2:
            break
        arr.append(i)

    assert arr == [0,1]


def for_with_continue():
    arr = []
    for i in range(4):
        if i == 2:
            continue
        arr.append(i)

    assert arr == [0,1,3]

# Does not translate
def for_with_else():
    arr = []
    for i in range(4):
        arr.append(i)
    else:
        arr.append(4)

    assert arr == [0,1,2,3,4]


def while_with_break():
    arr = []
    i = 0
    while True:
        if i == 2:
            break
        arr.append(i)
        i += 1

    assert arr == [0,1]


def while_with_continue():
    arr = []
    i = 0
    while i < 5:
        i += 1
        if i == 2:
            continue
        arr.append(i)

    assert arr == [1,3,4,5]

def loop_range_test():
    arr1 = []
    for i in range(1,10):
        arr1.append(i)
    arr2 = []
    num = range(1,12)
    for i in num:
        arr2.append(i)
    
    assert arr1 == [1,2,3,4,5,6,7,8,9]
    assert arr2 == [1,2,3,4,5,6,7,8,9,10,11]

def loop_element_test():
    arr = [1,2,3]
    arr1 = []
    for e in arr:
        e[1]
        arr1.append(e)
    
    assert arr1 == [1,2,3]

def loop_element_test_2():
    arr = [1,2]
    arr_c = [2,3,4]
    arr1 = []
    for e in arr:
        arr1.append(arr_c[e])

    assert arr1 == [3,4]


if __name__ == "__main__":
    for_with_break()
    for_with_continue()
    # https://github.com/adsharma/py2many/issues/415
    # for_with_else()
    while_with_break()
    while_with_continue()
    loop_range_test()
    loop_element_test_2()
