
# Unsupported in ast
def bitwise_not_int():
    a: int = 2
    return ~a


if __name__ == "__main__":
    assert bitwise_not_int() == -3 # --> Currently unsupported
    -1 # unary op test

