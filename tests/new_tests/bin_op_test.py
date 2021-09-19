from typing import List

def show_res():
    a: List[int] = []
    for i in range(0, 10):
        a.append(i)

    return 2*a

if __name__ == "__main__":
    print(show_res())