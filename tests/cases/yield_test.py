# @resumable # For PyJL
def generator_func():
    num = 1
    yield num
    num = 5
    yield num
    num = 10
    yield num

# @resumable
def generator_func_loop():
    num = 0
    for n in range(0, 3):
        yield num + n

# @resumable
def generator_func_loop_using_var():
    num = 0
    end = 2
    end = 3 # should get last variable assignment
    for n in range(0, end):
        yield num + n

# @resumable
def generator_func_nested_loop():
    for n in range(0, 2):
        for i in range(0, 2):
            yield (n,i)

# @resumable
def file_reader(file_name:str):
    for file_row in open(file_name, "r"):
        yield file_row

# @resumable
def testgen():
    print("first")
    yield 1
    print("second")
    yield 2

# @resumable
def fib():
    a = 0
    b = 1
    while True:
        yield a
        a, b = b, a+b

class TestClass:
    # @resumable
    def generator_func(self):
        num = 123
        yield num
        num = 5
        yield num
        num = 10
        yield num

if __name__ == "__main__":
    # Calling functions normally (Supported)
    arr1 = []
    for i in generator_func():
        arr1.append(i)
    assert arr1 == [1, 5, 10]

    # -----------------------
    arr2 = []
    for i in generator_func_loop():
        arr2.append(i)
    assert arr2 == [0, 1, 2]

    # -----------------------
    arr3 = []
    for i in generator_func_loop_using_var():
        arr3.append(i)
    assert arr3 == [0, 1, 2]

    # -----------------------
    # Testing with class scope
    arr4 = []
    testClass1: TestClass = TestClass()
    for i in testClass1.generator_func():
        arr4.append(i)
    assert arr4 == [123, 5, 10]

    # -----------------------
    # Testing nested loop
    arr5 = []
    for i in generator_func_nested_loop():
        arr5.append(i)
    assert arr5 == [(0,0), (0,1), (1,0), (1,1)]

    # -----------------------
    arr6 = []
    # Create file before executing
    for res in file_reader("C:/Users/Miguel Marcelino/Desktop/test.txt"):
        arr6.append(res)
    assert arr6 == ['test\n', 'test\n', 'test']

    # -----------------------
    arr7 = []
    res = fib()
    for i in range(0,6):
        arr7.append(res.__next__())
    assert arr7 == [0,1,1,2,3,5]

    # -----------------------
    for i in testgen():
        print(i)

    
    # -----------------------------------
    # Calling functions using loop (unsupported in PyJL)
    # testClass2: TestClass = TestClass()
    # funcs = [generator_func, generator_func_loop, generator_func_loop_using_var, testClass2.generator_func,
    #     generator_func_nested_loop]
    # arrL = []
    # for func in funcs:
    #     for i in func():
    #         arrL.append(i)

    # assert arrL == [1, 5, 10, 0, 1, 2, 0, 1, 2, 123, 5, 10, (0,0), (0,1), (1,0), (1,1)]