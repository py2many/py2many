from typing import List

def show_res():
    a: List[int] = []
    for i in range(0, 10):
        a.append(i)

    # a: int = 2
    return a*2

if __name__ == "__main__":
    print(show_res())