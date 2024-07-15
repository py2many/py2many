#!/usr/bin/env python3

CODE_0 = 0
CODE_1 = 1

L_A = [CODE_0, CODE_1]

CODE_A = "a"
CODE_B = "b"

L_B = [CODE_A, CODE_B]

if __name__ == "__main__":
    for i in L_A:
        print(i)
    for j in L_B:
        print(j)
    # test for container membership
    if "a" in ["a", "b"]:
        print("OK")
