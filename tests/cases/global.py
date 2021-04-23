code_0 = 0
code_1 = 1

l_a = [
    code_0,
    code_1,
]

code_a = "a"
code_b = "b"

l_b = [
    code_a,
    code_b,
]

if __name__ == "__main__":
    for i in l_a:
        print(i)
    for i in l_b:
        print(i)
    # test for container membership
    if "a" in ["a", "b"]:
        print("OK")

