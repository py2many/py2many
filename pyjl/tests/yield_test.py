def generator_func():
    num = 1
    yield num
    num = 5
    yield num
    num = 10
    yield num

if __name__ == "__main__":
    generator_func()