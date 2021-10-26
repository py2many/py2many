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

def generator_func_loop_using_var():
    num = 0
    end = 12
    end = 16
    for n in range(1, end):
        yield num + n

class TestClass:
    def generator_func(self, ola: int):
        num = 1
        yield num
        num = 5
        yield num
        num = 10
        yield num

if __name__ == "__main__":
    for i in generator_func():
        print(i)
    print("-----------------------")
    for i in generator_func_loop():
        print(i)
    print("-----------------------")
    for i in generator_func_loop_using_var():
        print(i)
    print("-----------------------")
    testClass = TestClass()
    generator_func(testClass, 123) # Does not work
    for i in generator_func(testClass, 123):
        print(i)