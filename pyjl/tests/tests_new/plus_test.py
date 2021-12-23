# Runtime information
def plus_test(x, y):
    return x + y

# Compile time information
def plus_test(x:str, y:str):
    return x + y

if __name__ == "__main__":
    x = "ss"
    y = "zz"
    res = plus_test(x, y)
    assert res == "sszz"
    print("OK")