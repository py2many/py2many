@use_continuables
def generator_func():
    num = 1
    yield num
    num = 5
    yield num
    num = 10
    yield num

if __name__ == "__main__":
    for i in generator_func():
        print(i)