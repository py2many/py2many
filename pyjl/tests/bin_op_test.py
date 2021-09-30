from typing import List

def mult_int_and_int():
    a = 2
    return a*2

def mult_float_and_int():
    a = 2.0
    return a*2

def mult_list_and_int():
    a: List[int] = []
    for i in range(0, 10):
        a.append(i)

    # a: int = 2 # Should fail if uncommented
    return a*2

def add_two_lists():
    a: List[int] = []
    b: List[int] = []
    for i in range(0, 10):
        a.append(i)
        b.append(i)

    return a+b

if __name__ == "__main__":
    print(mult_int_and_int())
    print(mult_float_and_int())
    print(mult_list_and_int())
    print(add_two_lists())