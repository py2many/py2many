from typing import List

def show_res():
    a: List[int] = []
    for i in range(0, 10):
        a.append(i)

    # a: int = 2
    return a*2

def show_res_add_two_lists():
    a: List[int] = []
    b: List[int] = []
    for i in range(0, 10):
        a.append(i)
        b.append(i)

    return a+b

if __name__ == "__main__":
    print(show_res())
    print(show_res_add_two_lists())