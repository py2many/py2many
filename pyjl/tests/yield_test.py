# @use_continuables
def generator_func():
    num = 1
    yield num
    num = 5
    yield num
    num = 10
    yield num


def generator_func_loop():
    num = 0
    for n in range(1, 10):
        yield num + n

if __name__ == "__main__":
    for i in generator_func():
        print(i)
    print("-----------------------")
    for i in generator_func_loop():
        print(i)