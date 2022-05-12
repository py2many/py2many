
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
    # 1
    arr = [1,2]
    res_1 = []
    for e in arr:
        e[1]
        res_1.append(e)
    
    assert res_1 == [1,2]

    # 2
    arr_c = [2,3,4]
    res_2 = []
    for e in arr:
        res_2.append(arr_c[e])

    assert res_2 == [3,4]

def for_cycle_vars():
    seq = [1,2,3,4,5] 
    seq_copy = list(seq)
    for i in range(len(seq) - 1):
        # Assert that the list has not changed
        assert seq[i] == seq_copy[i]

    # Test loop getting elements
    complex_list = [([1,2],3,4)]
    for [(a1,a2), b, c] in complex_list:
        assert a1 == 1
        assert a2 == 2
        assert b == 3
        assert c == 4

        # Test nested loop
        arr = []
        a = 1
        for j in range(0,2):
            arr.append(a)
            a += 1
        
        assert arr[0] == 1
        assert arr[1] == 2
    
    # Test limit access
    assert seq[0] == 1 # First value
    assert seq[2] == 3 # Some value in the middle
    assert seq[-1] == 5 # Last Value
    
    x = 1
    assert seq[x] == 2

def reversed_array():
    x = [1,2,3]
    x = x[::-1]
    assert x ==[3,2,1]

def list_of_lists():
    x = [[1,2],[3,4,5,6],[3,4,5,6]]
    assert (x[1][2]) == 5
    assert (x[2][3]) == 6

def inplace_ops():
    a = [1, 1]
    b = a; 
    b += [3, 3]
    assert a == [1, 1, 3, 3]
    assert b == [1, 1, 3, 3]

def list_ops():
    a = list()

    # Append
    a.append("test")
    assert a == ["test"]

    # Clear
    a.clear()
    assert a == []
    assert len(a) == 0

    # Remove
    a.append("test1")
    a.append("test2")
    a.remove("test1")
    assert a == ["test2"]
    assert len(a) == 1
    a.clear() # reset list

    # Copy
    a.append("test")
    b = a.copy()
    assert b == a
    a.clear() # reset list

    # Count
    a.append("test2")
    a.append("test2")
    a.remove("test2")
    assert a.count("test2") == 1
    a.clear() # reset list

    # Extend
    a.append("test1")
    a.extend(b)
    assert a == ["test1", "test"]
    a.clear() # reset list

    # List Multiplication
    elems = ["1", "2", "3"]
    new_elems = []
    for e in elems:
        new_elems.append(e*2)
    assert new_elems == ["11", "22", "33"]

if __name__ == "__main__":
    for_with_break()
    for_with_continue()
    # https://github.com/adsharma/py2many/issues/415
    # for_with_else()
    while_with_break()
    while_with_continue()
    loop_range_test()
    for_cycle_vars()
    reversed_array()
    list_of_lists()
    inplace_ops()
    list_ops()
