from typing import List


def indexing():
    sum = 0
    a: List[int] = []
    for i in range(10):
        a.append(i)
        sum += a[i]
    return sum


def show():
    # assign
    a1 = 10
    # annotated assign
    a2: float = 2.1
    print(a2)
    # for loop
    for i in range(0, 10):
        print(i)
    for i in range(0, 10, 2):
        print(i)
    # unary op
    a3 = -a1
    # binary op
    a4 = a3 + a1
    print(a4)
    sum1 = indexing()
    print(sum1)
    # Uncomment as we fix things
    # lists, sets and dict
    a5 = [1, 2, 3]
    print(len(a5))
    # a6 = {1, 2, 3, 4}
    # print(len(a6))
    # a7 = {"a": 1, "b": 2}
    # print(len(a7))
    # a8 = True
    # if a8:
    #     print("true")
    # elif a4 > 0:
    #     print("never get here")
    # if a1 == 11:
    #     print("false")
    # else:
    #     print("true")


if __name__ == "__main__":
    show()
