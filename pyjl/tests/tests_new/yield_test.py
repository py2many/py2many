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
    def generator_func(self):
        num = 123
        yield num
        num = 5
        yield num
        num = 10
        yield num

if __name__ == "__main__":
    # Calling functions normally (Supported)
    for i in generator_func():
        print(i)
    print("-----------------------")
    for i in generator_func_loop():
        print(i)
    print("-----------------------")
    for i in generator_func_loop_using_var():
        print(i)
    print("-----------------------")
    testClass1: TestClass = TestClass()
    for i in testClass1.generator_func():
        print(i)
    
    # Calling functions using loop (currently not supported)
    testClass2: TestClass = TestClass()
    funcs = [generator_func, generator_func_loop, generator_func_loop_using_var, testClass2.generator_func]
    for func in funcs:
        for i in func():
            print(i)